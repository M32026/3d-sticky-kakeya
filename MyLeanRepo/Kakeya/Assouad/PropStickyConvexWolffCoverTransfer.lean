import MyLeanRepo.Kakeya.Assouad.PropStickyStatements

/-!
# Convex-Wolff transfer through a uniform assigned cover

This is the indexed finite version of the paper observation:

> if `B` satisfies the Convex Wolff Axioms with error `C`, and `A` is a
> `K`-uniform partitioning cover of `B`, then `A` satisfies the Convex Wolff
> Axioms with error `KC`.

The geometric input is stated as literal carrier containment.  This keeps the
finite counting theorem independent of any particular tube-cover convention.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped ENNReal
open MeasureTheory

attribute [local instance] Classical.propDecidable

/--
Transfer the normalized cropped-paper Convex-Wolff bound from a fine family to
an assigned coarse family.
-/
theorem paperConvexWolffBound_of_uniform_cover
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin fine.card → Fin coarse.card)
    (parent_surjective : Function.Surjective parent)
    (carrier_contained :
      ∀ source,
        wz1PaperTubeCarrier (fine.tube source) ⊆
          wz1PaperTubeCarrier (coarse.tube (parent source)))
    (K C : ENNReal)
    (fiber_uniform :
      ∀ first second,
        ((Finset.univ.filter fun source =>
          parent source = first).card : ENNReal) ≤
          K *
            ((Finset.univ.filter fun source =>
              parent source = second).card : ENNReal))
    (hfine : WZ2PaperConvexWolffBound fine C) :
    WZ2PaperConvexWolffBound coarse (K * C) := by
  intro convexSet hconvex
  let coarseContained : Finset (Fin coarse.card) :=
    Finset.univ.filter fun coarseIndex =>
      wz1PaperTubeCarrier (coarse.tube coarseIndex) ⊆ convexSet
  let fineContained : Finset (Fin fine.card) :=
    Finset.univ.filter fun source =>
      wz1PaperTubeCarrier (fine.tube source) ⊆ convexSet
  have hparentContained :
      ∀ source, parent source ∈ coarseContained →
        source ∈ fineContained := by
    intro source hparent
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ source,
        (carrier_contained source).trans
          (Finset.mem_filter.mp hparent).2⟩
  by_cases hcoarse_empty : coarse.card = 0
  · have hcontained_zero :
        (wz1PaperBodyFamily coarse).containedCount convexSet = 0 := by
      unfold Kakeya.Streamlined.BodyFamily.containedCount
      have hindices_empty :
          (wz1PaperBodyFamily coarse).containedIndices convexSet = ∅ := by
        ext index
        have hzero : index.1 < 0 := by
          have hbound := index.2
          change index.1 < coarse.card at hbound
          rw [hcoarse_empty] at hbound
          exact hbound
        omega
      rw [hindices_empty]
      simp
    rw [hcontained_zero]
    exact bot_le
  · have hcoarse_nonempty : Nonempty (Fin coarse.card) := by
      exact ⟨⟨0, Nat.pos_of_ne_zero hcoarse_empty⟩⟩
    let fiber : Fin coarse.card → Finset (Fin fine.card) :=
      fun coarseIndex =>
        Finset.univ.filter fun source =>
          parent source = coarseIndex
    obtain ⟨reference, _href_mem, hreference_min⟩ :=
      Finset.exists_min_image
        (Finset.univ : Finset (Fin coarse.card))
        (fun coarseIndex => (fiber coarseIndex).card)
        Finset.univ_nonempty
    let referenceFiber := fiber reference
    have hreference_nonempty : referenceFiber.Nonempty := by
      rcases parent_surjective reference with ⟨source, hsource⟩
      exact
        ⟨source, Finset.mem_filter.mpr
          ⟨Finset.mem_univ source, hsource⟩⟩
    have hreference_pos :
        0 < (referenceFiber.card : ENNReal) := by
      exact_mod_cast Finset.card_pos.mpr hreference_nonempty
    have hreference_top :
        (referenceFiber.card : ENNReal) ≠ ⊤ := by
      simp
    have hcoarse_to_fine_nat :
        coarseContained.card * referenceFiber.card ≤
          fineContained.card := by
      let selectedFine :=
        Finset.univ.filter fun source =>
          parent source ∈ coarseContained
      have hselected_subset :
          selectedFine ⊆ fineContained := by
        intro source hsource
        exact hparentContained source
          (Finset.mem_filter.mp hsource).2
      have hsum_eq :
          ∑ coarseIndex ∈ coarseContained,
              (fiber coarseIndex).card =
            selectedFine.card := by
        simpa only [fiber, selectedFine] using
          Finset.sum_card_fiberwise_eq_card_filter
            (Finset.univ : Finset (Fin fine.card))
            coarseContained parent
      calc
        coarseContained.card * referenceFiber.card =
            ∑ _coarseIndex ∈ coarseContained,
              referenceFiber.card := by
          simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ coarseIndex ∈ coarseContained,
              (fiber coarseIndex).card := by
          exact Finset.sum_le_sum fun coarseIndex hcoarseIndex =>
            hreference_min coarseIndex
              (Finset.mem_univ coarseIndex)
        _ = selectedFine.card := hsum_eq
        _ ≤ fineContained.card :=
          Finset.card_le_card hselected_subset
    have hcoarse_to_fine :
        (coarseContained.card : ENNReal) *
            (referenceFiber.card : ENNReal) ≤
          (fineContained.card : ENNReal) := by
      exact_mod_cast hcoarse_to_fine_nat
    have hfine_bound :
        (fineContained.card : ENNReal) ≤
          C * volume convexSet * fine.enncard := by
      have h := hfine convexSet hconvex
      change
        ((Finset.univ.filter fun source : Fin fine.card =>
            wz1PaperTubeCarrier (fine.tube source) ⊆ convexSet).card :
              ENNReal) ≤
          C * volume convexSet * fine.enncard at h
      exact h
    have htotal_fibers :
        (fine.card : ENNReal) ≤
          K * (coarse.card : ENNReal) *
            (referenceFiber.card : ENNReal) := by
      let allCoarse : Finset (Fin coarse.card) := Finset.univ
      have hsum_eq :
          ∑ coarseIndex ∈ allCoarse,
              (fiber coarseIndex).card =
            fine.card := by
        simpa only [fiber] using
          (Finset.sum_card_fiberwise_eq_card_filter
            (Finset.univ : Finset (Fin fine.card))
            allCoarse parent).trans (by simp [allCoarse])
      have hsum_upper :
          ∑ coarseIndex ∈ allCoarse,
              ((fiber coarseIndex).card : ENNReal) ≤
            ∑ _coarseIndex ∈ allCoarse,
              K * (referenceFiber.card : ENNReal) := by
        exact Finset.sum_le_sum fun coarseIndex _ => by
          simpa [fiber, referenceFiber] using
            fiber_uniform coarseIndex reference
      rw [show (fine.card : ENNReal) =
          ∑ coarseIndex ∈ allCoarse,
            ((fiber coarseIndex).card : ENNReal) by
        exact_mod_cast hsum_eq.symm]
      calc
        ∑ coarseIndex ∈ allCoarse,
            ((fiber coarseIndex).card : ENNReal)
            ≤ ∑ _coarseIndex ∈ allCoarse,
                K * (referenceFiber.card : ENNReal) := hsum_upper
        _ = K * (coarse.card : ENNReal) *
            (referenceFiber.card : ENNReal) := by
          simp [allCoarse, Finset.sum_const, nsmul_eq_mul]
          ring
    have htotal_fibers' :
        fine.enncard ≤
          K * (coarse.card : ENNReal) *
            (referenceFiber.card : ENNReal) := by
      simpa [Kakeya.Streamlined.TubeFamily.enncard] using
        htotal_fibers
    have hwith_reference :
        (coarseContained.card : ENNReal) *
            (referenceFiber.card : ENNReal) ≤
          ((K * C) * volume convexSet *
            (coarse.card : ENNReal)) *
              (referenceFiber.card : ENNReal) := by
      calc
        (coarseContained.card : ENNReal) *
              (referenceFiber.card : ENNReal)
            ≤ (fineContained.card : ENNReal) :=
          hcoarse_to_fine
        _ ≤ C * volume convexSet * fine.enncard :=
          hfine_bound
        _ ≤ C * volume convexSet *
            (K * (coarse.card : ENNReal) *
              (referenceFiber.card : ENNReal)) := by
          gcongr
        _ = ((K * C) * volume convexSet *
              (coarse.card : ENNReal)) *
            (referenceFiber.card : ENNReal) := by ring
    have hcoarse_bound :
        (coarseContained.card : ENNReal) ≤
          (K * C) * volume convexSet *
            (coarse.card : ENNReal) :=
      (ENNReal.mul_le_mul_iff_left
        hreference_pos.ne' hreference_top).mp
        hwith_reference
    change
      ((Finset.univ.filter fun coarseIndex : Fin coarse.card =>
          wz1PaperTubeCarrier (coarse.tube coarseIndex) ⊆ convexSet).card :
            ENNReal) ≤
        (K * C) * volume convexSet * coarse.enncard
    simpa [Kakeya.Streamlined.TubeFamily.enncard] using hcoarse_bound

end Kakeya.Assouad

end
