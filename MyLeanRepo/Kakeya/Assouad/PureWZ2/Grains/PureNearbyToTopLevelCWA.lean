import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.PropStickyStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingJacobian
import Mathlib.Analysis.Convex.Measure
import Mathlib.Tactic

/-!
# Pure nearby-scales CWA to top-level Convex-Wolff bound

Analog of `wz2_paper_nearby_top_level_convex_wolff_canonical` for the
**pure** Definition 2.12 formulation.

Given `WZ2PaperPureCWAAtNearbyScales family C`, produce
`WZ2PaperConvexWolffBound family (4 * C)` by requesting scale 1 and
transferring the normalized fiber CWA back via the inverse Assouad
normalization map.

## Key facts

1. Requesting scale `rho₀ = 1` returns a cover with `rho ≥ 1`.
2. The Assouad normalization map has determinant `≤ 4 / rho² ≤ 4`
   (from `wz2Paper_outerJohn_abs_det_lower`).
3. Each fiber's normalized CWA transfers back with constant factor `≤ 4`.
4. The full fibers partition the fine family (from `covers` +
   `doubled_fibers_disjoint`), so the fiber bounds assemble to the
   full-family bound.

## Whiteprint

Supports node `wz2_node05_c2_grains`, specifically the top-level CWA
field without the M⁶ envelope budget.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set MeasureTheory Finset

attribute [local instance] Classical.propDecidable

/-- Transfer CWA from the normalized fiber body family back to the
original full fiber, using the bounded determinant of the Assouad
normalization map. -/
lemma pure_fiber_cwa_transfer
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card)
    (normalization : WZ2PaperAssouadUnitRescalingData (coarse.tube parent))
    (hrho_one : 1 ≤ rho)
    {C : ENNReal}
    (hCWA : WZ2PaperBodyConvexWolffBound
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := fine) (coarse := coarse) parent normalization) C)
    (K : Set Point3) (hK : Convex ℝ K) :
    ((wz2PaperOrdinaryFullFiberIndices fine coarse parent).filter
      fun i => (fine.tube i).carrier ⊆ K).card ≤
    (4 : ENNReal) * C * volume K *
      (wz2PaperOrdinaryFullFiberIndices fine coarse parent).card := by
  let f := normalization.map
  let fLin : Point3 →ₗ[ℝ] Point3 := (f.linear : Point3 →ₗ[ℝ] Point3)
  let v : Point3 := f 0
  have h_decomp : ∀ (x : Point3), f x = fLin x + v := by
    intro x
    have h : fLin (x - (0 : Point3)) = f x - f 0 :=
      f.toAffineMap.linearMap_vsub x (0 : Point3)
    have h' : fLin x = f x - v := by simpa [fLin, v, sub_zero] using h
    exact eq_add_of_sub_eq h'.symm
  let E := f '' K
  have hE_convex : Convex ℝ E := hK.affine_image f.toAffineMap
  let normBF := wz2PaperPureUnitRescaledFullFiberBodyFamily
    (fine := fine) (coarse := coarse) parent normalization
  let idxEquiv := wz2PaperOrdinaryFullFiberIndexEquiv
    (fine := fine) (coarse := coarse) (parent := parent)

  -- Containment equivalence: normalized body ⊆ E iff original tube ⊆ K
  have h_contain_iff : ∀ (target : Fin normBF.card),
      (normBF.body target).carrier ⊆ E ↔
        (fine.tube ((idxEquiv target).1)).carrier ⊆ K := by
    intro target
    let source := (idxEquiv target).1
    have h_eq : (normBF.body target).carrier = f '' (fine.tube source).carrier := by rfl
    rw [h_eq]
    constructor
    · intro h
      exact Set.image_subset_image_iff f.injective |>.mp h
    · intro h
      exact Set.image_mono h

  -- Contained count equality via bijection g
  let g : Fin normBF.card → Fin fine.card := fun target => (idxEquiv target).1
  let S1 : Finset (Fin normBF.card) :=
    Finset.univ.filter (fun target => (normBF.body target).carrier ⊆ E)
  let S2 : Finset (Fin fine.card) :=
    (wz2PaperOrdinaryFullFiberIndices fine coarse parent).filter
      (fun i => (fine.tube i).carrier ⊆ K)
  have h_inj : Set.InjOn g S1 := by
    intro t1 _ t2 _ h
    have h' : (idxEquiv t1).1 = (idxEquiv t2).1 := h
    have h'' : idxEquiv t1 = idxEquiv t2 := by
      apply Subtype.ext
      exact h'
    exact idxEquiv.injective h''
  have h_image : Finset.image g S1 = S2 := by
    ext source
    simp only [S1, S2, g, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨target, htarget, rfl⟩
      exact ⟨(idxEquiv target).2, (h_contain_iff target).mp htarget⟩
    · rintro ⟨h_in_full, h_contain⟩
      let target : Fin normBF.card := idxEquiv.symm ⟨source, h_in_full⟩
      have h_gs : g target = source := by
        simp [g, target, idxEquiv]
      have h_source_eq : (idxEquiv target).1 = source := h_gs
      have h_contain' : (fine.tube (idxEquiv target).1).carrier ⊆ K := by
        rw [h_source_eq]
        exact h_contain
      have h_target_contain : (normBF.body target).carrier ⊆ E :=
        (h_contain_iff target).mpr h_contain'
      exact ⟨target, h_target_contain, h_gs⟩
  have h_card_eq : normBF.containedCount E = S2.card := by
    have h_eq1 : normBF.containedCount E = S1.card := by
      simp [Kakeya.Streamlined.BodyFamily.containedCount,
        Kakeya.Streamlined.BodyFamily.containedIndices, S1]
    rw [h_eq1]
    have h_eq2 : S1.card = (Finset.image g S1).card :=
      (Finset.card_image_of_injOn h_inj).symm
    rw [h_eq2, h_image]

  -- Determinant bound: |det(fLin)| ≤ 4 / rho² ≤ 4
  let J := normalization.parent_convex_body.outerJohnEllipsoidMap
  have hJ1 : |LinearMap.det (J : Point3 →ₗ[ℝ] Point3)| ≥ rho ^ 2 / 4 :=
    wz2Paper_outerJohn_abs_det_lower (coarse.tube parent) (by linarith)
  have h2 : fLin = (J.symm : Point3 →ₗ[ℝ] Point3) := by rfl
  have h_det_bound : |LinearMap.det fLin| ≤ (4 : ℝ) := by
    rw [h2]
    have h3 : |LinearMap.det (J.symm : Point3 →ₗ[ℝ] Point3)| =
        1 / |LinearMap.det (J : Point3 →ₗ[ℝ] Point3)| := by
      have h31 : LinearMap.det (J.symm : Point3 →ₗ[ℝ] Point3) =
          (LinearMap.det (J : Point3 →ₗ[ℝ] Point3))⁻¹ :=
        LinearEquiv.det_coe_symm J
      rw [h31]
      have h_pos : 0 < |LinearMap.det (J : Point3 →ₗ[ℝ] Point3)| := by
        have h41 : LinearMap.det (J : Point3 →ₗ[ℝ] Point3) ≠ 0 := by
          have h_comp : (J : Point3 →ₗ[ℝ] Point3).comp (J.symm : Point3 →ₗ[ℝ] Point3) = .id := by
            ext z; simp
          have h_det_comp : LinearMap.det ((J : Point3 →ₗ[ℝ] Point3).comp (J.symm : Point3 →ₗ[ℝ] Point3)) = 1 := by
            rw [h_comp]; simp
          have h_mul : LinearMap.det (J : Point3 →ₗ[ℝ] Point3) * LinearMap.det (J.symm : Point3 →ₗ[ℝ] Point3) = 1 := by
            rw [← LinearMap.det_comp]; exact h_det_comp
          intro h
          rw [h] at h_mul
          norm_num at h_mul
        exact abs_pos.mpr h41
      rw [abs_inv]
      <;> field_simp
    rw [h3]
    have h5 : 1 / |LinearMap.det (J : Point3 →ₗ[ℝ] Point3)| ≤ 1 / (rho ^ 2 / 4) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    have h6 : 1 / (rho ^ 2 / 4) = 4 / rho ^ 2 := by
      field_simp
    rw [h6] at h5
    have h7 : 4 / rho ^ 2 ≤ 4 := by
      have h8 : 1 ≤ rho ^ 2 := by nlinarith
      have h9 : 4 / rho ^ 2 ≤ 4 / (1 : ℝ) := by gcongr
      have h10 : 4 / (1 : ℝ) = 4 := by norm_num
      rw [h10] at h9
      exact h9
    linarith

  -- Convex image and measurable set
  have h_conv_image : Convex ℝ (fLin '' K) := hK.linear_image fLin
  have h_nms : NullMeasurableSet (fLin '' K) volume :=
    h_conv_image.nullMeasurableSet volume

  -- Volume bound: volume E ≤ 4 * volume K
  have h_vol : volume E ≤ (4 : ENNReal) * volume K := by
    have h1 : volume (fLin '' K) =
        ENNReal.ofReal (|LinearMap.det fLin|) * volume K :=
      MeasureTheory.Measure.addHaar_image_linearMap volume fLin K
    have h2 : E = (fun x : Point3 => v + x) '' (fLin '' K) := by
      ext y
      simp only [E, Set.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨fLin x, ⟨x, hx, rfl⟩, ?_⟩
        rw [h_decomp x] <;> abel
      · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
        refine ⟨x, hx, ?_⟩
        rw [h_decomp x] <;> abel
    rw [h2]
    have h_preimage : (fun x : Point3 => v + x) '' (fLin '' K) =
        (fun x : Point3 => x + (-v)) ⁻¹' (fLin '' K) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simp only [Set.mem_preimage]
        have h_ye : (v + x) + (-v) = x := by abel
        rw [h_ye]
        exact hx
      · intro hx
        have h_goal : v + (y + (-v)) = y := by abel
        exact ⟨y + (-v), hx, h_goal⟩
    rw [h_preimage]
    have hmp : MeasurePreserving (fun x : Point3 => x + (-v)) volume volume :=
      MeasureTheory.measurePreserving_add_right volume (-v)
    have h4 : volume ((fun x : Point3 => x + (-v)) ⁻¹' (fLin '' K)) = volume (fLin '' K) :=
      hmp.measure_preimage h_nms
    rw [h4, h1]
    have h9 : ENNReal.ofReal (|LinearMap.det fLin|) ≤ (4 : ENNReal) := by
      have h10 : ENNReal.ofReal (|LinearMap.det fLin|) ≤ ENNReal.ofReal (4 : ℝ) :=
        ENNReal.ofReal_le_ofReal h_det_bound
      have h11 : ENNReal.ofReal (4 : ℝ) = (4 : ENNReal) := by simp
      rw [h11] at h10
      exact h10
    have h12 : ENNReal.ofReal (|LinearMap.det fLin|) * volume K ≤ (4 : ENNReal) * volume K := by
      exact mul_le_mul_of_nonneg_right h9 bot_le
    exact h12

  -- Main CWA bound for normalized fiber
  have h_main : normBF.containedCount E ≤ C * volume E * normBF.enncard :=
    hCWA E hE_convex

  -- Transfer back
  have h_enncard_eq : normBF.enncard =
      (↑((wz2PaperOrdinaryFullFiberIndices fine coarse parent).card) : ENNReal) := by
    simp [normBF, Kakeya.Streamlined.BodyFamily.enncard] <;> rfl
  have h_main2 : (↑(normBF.containedCount E) : ENNReal) ≤
      C * volume E * (↑((wz2PaperOrdinaryFullFiberIndices fine coarse parent).card) : ENNReal) := by
    rw [h_enncard_eq] at h_main
    exact h_main
  have h_final : (↑(S2.card) : ENNReal) ≤
      (4 : ENNReal) * C * volume K *
        (↑((wz2PaperOrdinaryFullFiberIndices fine coarse parent).card) : ENNReal) := by
    calc
      (↑(S2.card) : ENNReal)
        = ↑(normBF.containedCount E) := by exact_mod_cast h_card_eq.symm
      _ ≤ C * volume E * (↑((wz2PaperOrdinaryFullFiberIndices fine coarse parent).card) : ENNReal) := h_main2
      _ ≤ C * ((4 : ENNReal) * volume K) * (↑((wz2PaperOrdinaryFullFiberIndices fine coarse parent).card) : ENNReal) := by
          gcongr
      _ = (4 : ENNReal) * C * volume K * (↑((wz2PaperOrdinaryFullFiberIndices fine coarse parent).card) : ENNReal) := by ring
  exact_mod_cast h_final

/-- The full fibers of a pure partitioning cover partition the fine index set. -/
lemma pure_full_fibers_partition
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (hrho_pos : 0 < rho)
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (P : Fin fine.card → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      ∑ p : Fin coarse.card,
        ((wz2PaperOrdinaryFullFiberIndices fine coarse p).filter P).card := by
  let fullFiber := fun p : Fin coarse.card =>
    wz2PaperOrdinaryFullFiberIndices fine coarse p
  -- Helper: any tube carrier is contained in its 2-centered dilation
  have h_self_dil : ∀ (tube : Kakeya.DeltaTube rho),
      tube.carrier ⊆ wz2PaperCenteredDilatedCarrier 2 tube :=
    fun tube => wz2_paper_carrier_subset_centeredDilatedTwo tube hrho_pos.le
  -- Full fibers are disjoint (since they're subsets of disjoint dilated fibers)
  have h_disj : ∀ (p q : Fin coarse.card), p ≠ q →
      Disjoint (fullFiber p) (fullFiber q) := by
    intro p q hpq
    have h3 : Disjoint (wz2PaperOrdinaryDilatedFiberIndices 2 fine coarse p)
        (wz2PaperOrdinaryDilatedFiberIndices 2 fine coarse q) :=
      cover.doubled_fibers_disjoint p q hpq
    have h4 : fullFiber p ⊆ wz2PaperOrdinaryDilatedFiberIndices 2 fine coarse p := by
      intro i hi
      have h5 : (fine.tube i).carrier ⊆ (coarse.tube p).carrier :=
        (Finset.mem_filter.mp hi).2
      have h6 : (fine.tube i).carrier ⊆ wz2PaperCenteredDilatedCarrier 2 (coarse.tube p) :=
        h5.trans (h_self_dil (coarse.tube p))
      have h7 : i ∈ wz2PaperOrdinaryDilatedFiberIndices 2 fine coarse p := by
        simp only [wz2PaperOrdinaryDilatedFiberIndices, Finset.mem_filter]
        exact ⟨(Finset.mem_filter.mp hi).1, h6⟩
      exact h7
    have h5 : fullFiber q ⊆ wz2PaperOrdinaryDilatedFiberIndices 2 fine coarse q := by
      intro i hi
      have h6 : (fine.tube i).carrier ⊆ (coarse.tube q).carrier :=
        (Finset.mem_filter.mp hi).2
      have h7 : (fine.tube i).carrier ⊆ wz2PaperCenteredDilatedCarrier 2 (coarse.tube q) :=
        h6.trans (h_self_dil (coarse.tube q))
      have h8 : i ∈ wz2PaperOrdinaryDilatedFiberIndices 2 fine coarse q := by
        simp only [wz2PaperOrdinaryDilatedFiberIndices, Finset.mem_filter]
        exact ⟨(Finset.mem_filter.mp hi).1, h7⟩
      exact h8
    exact Disjoint.mono h4 h5 h3
  -- Filtered full fibers are also pairwise disjoint
  have h_disj_filter : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin coarse.card)))
      fun p => (fullFiber p).filter P := by
    intro p _ q _ hpq
    have h : Disjoint (fullFiber p) (fullFiber q) := h_disj p q hpq
    exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) h
  -- The union of filtered full fibers equals the filtered univ
  have h_union : (Finset.univ.filter P) =
      Finset.biUnion (Finset.univ : Finset (Fin coarse.card))
        fun p => (fullFiber p).filter P := by
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      rcases cover.covers i with ⟨p, hp⟩
      exact ⟨p, ⟨hp, hi⟩⟩
    · rintro ⟨p, hfilter⟩
      exact hfilter.2
  rw [h_union]
  rw [Finset.card_biUnion h_disj_filter]
  <;> rfl

/-- Convert pure nearby-scales CWA to an ordinary top-level Convex-Wolff bound
(using `.carrier`, not `wz1PaperTubeCarrier`).

The constant factor is `4`, coming from the determinant bound on the
Assouad normalization map at scale `rho ≥ 1`. -/
theorem pure_nearby_to_top_level_ordinary
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hPureNearby : WZ2PaperPureCWAAtNearbyScales family C) :
    WZ2PaperBodyConvexWolffBound family.toBodyFamily ((4 : ENNReal) * C) := by
  -- Request scale 1
  let rho₀ : WZ2PaperRequestedScale delta :=
    ⟨1, by linarith, by norm_num⟩
  rcases hPureNearby.2.2.2 rho₀ with ⟨coverData⟩
  let rho : ℝ := coverData.rho
  have hrho_one : 1 ≤ rho := coverData.requested_le
  let scaleData := coverData.scaleData
  let coarse := scaleData.coarse
  let cover := scaleData.cover
  let fine := family

  intro K hK

  -- For each parent, get the normalized fiber data and transfer CWA
  have h_fiber_bound : ∀ (p : Fin coarse.card),
      ((wz2PaperOrdinaryFullFiberIndices fine coarse p).filter
        fun i => (fine.tube i).carrier ⊆ K).card ≤
      (4 : ENNReal) * C * volume K *
        (wz2PaperOrdinaryFullFiberIndices fine coarse p).card := by
    intro p
    rcases scaleData.rescaledFiber p with ⟨fiberData⟩
    exact pure_fiber_cwa_transfer p fiberData.normalization hrho_one
      fiberData.convex_wolff K hK

  let P_carrier : Fin fine.card → Prop := fun i => (fine.tube i).carrier ⊆ K

  have hrho_pos : 0 < rho := by linarith
  -- Partition identity for carrier containment
  have h_partition_carrier := pure_full_fibers_partition hrho_pos cover P_carrier
  -- Partition identity for all indices (P = fun _ => True)
  have h_partition_all := pure_full_fibers_partition hrho_pos cover (fun _ => True)

  -- Sum of fiber sizes equals total card
  have h_card_sum : ∑ p : Fin coarse.card,
      (wz2PaperOrdinaryFullFiberIndices fine coarse p).card = fine.card := by
    have h := h_partition_all
    simpa [Finset.filter_true] using Eq.symm h

  -- Assemble the bound
  let a : ENNReal := (4 : ENNReal) * C * volume K
  have h1 : ((Finset.univ.filter P_carrier).card : ENNReal) =
      ∑ p : Fin coarse.card,
        (((wz2PaperOrdinaryFullFiberIndices fine coarse p).filter P_carrier).card : ENNReal) := by
    rw [h_partition_carrier, Nat.cast_sum]
  have h_sum : ∑ p : Fin coarse.card,
        (((wz2PaperOrdinaryFullFiberIndices fine coarse p).filter P_carrier).card : ENNReal) ≤
      ∑ p : Fin coarse.card,
        (a * ((wz2PaperOrdinaryFullFiberIndices fine coarse p).card : ENNReal)) := by
    apply Finset.sum_le_sum
    intro p _
    exact h_fiber_bound p
  have h_factor : ∑ p : Fin coarse.card,
        (a * ((wz2PaperOrdinaryFullFiberIndices fine coarse p).card : ENNReal)) =
      a * ∑ p : Fin coarse.card,
        ((wz2PaperOrdinaryFullFiberIndices fine coarse p).card : ENNReal) := by
    rw [Finset.mul_sum]
  have h_card_cast : (↑(∑ p : Fin coarse.card,
        (wz2PaperOrdinaryFullFiberIndices fine coarse p).card) : ENNReal) =
      ∑ p : Fin coarse.card,
        ((wz2PaperOrdinaryFullFiberIndices fine coarse p).card : ENNReal) := by
    rw [Nat.cast_sum]
  have h_enncard : (fine.card : ENNReal) = fine.enncard := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have h_main : ((Finset.univ.filter P_carrier).card : ENNReal) ≤
      a * fine.enncard := by
    calc
      ((Finset.univ.filter P_carrier).card : ENNReal)
        = ∑ p, (((wz2PaperOrdinaryFullFiberIndices fine coarse p).filter P_carrier).card : ENNReal) := h1
      _ ≤ ∑ p, (a * ((wz2PaperOrdinaryFullFiberIndices fine coarse p).card : ENNReal)) := h_sum
      _ = a * ∑ p, ((wz2PaperOrdinaryFullFiberIndices fine coarse p).card : ENNReal) := h_factor
      _ = a * (↑(∑ p, (wz2PaperOrdinaryFullFiberIndices fine coarse p).card) : ENNReal) := by rw [h_card_cast]
      _ = a * (fine.card : ENNReal) := by rw [h_card_sum]
      _ = a * fine.enncard := by rw [h_enncard]

  have h_goal : (family.toBodyFamily.containedCount K) =
      (Finset.univ.filter P_carrier).card := by
    simp [Kakeya.Streamlined.BodyFamily.containedCount,
      Kakeya.Streamlined.BodyFamily.containedIndices,
      Kakeya.Streamlined.TubeFamily.toBodyFamily, P_carrier]
    <;> rfl
  have h_enncard2 : family.toBodyFamily.enncard = fine.enncard := by
    simp [Kakeya.Streamlined.TubeFamily.toBodyFamily]
    <;> rfl
  rw [h_goal, h_enncard2]
  exact h_main

/-- Convert pure nearby-scales CWA to a cropped top-level Convex-Wolff bound.

Requires `family.IsInUnitBall` to convert from `.carrier` to
`wz1PaperTubeCarrier`. The constant factor is `4`. -/
theorem pure_nearby_to_top_level
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hsupport : family.IsInUnitBall)
    (hPureNearby : WZ2PaperPureCWAAtNearbyScales family C) :
    WZ2PaperConvexWolffBound family ((4 : ENNReal) * C) :=
  wz2_paper_ordinary_convexWolff_to_cropped
    hdelta.le hsupport
    (pure_nearby_to_top_level_ordinary hdelta hdeltaSmall hPureNearby)

end Kakeya.Assouad
