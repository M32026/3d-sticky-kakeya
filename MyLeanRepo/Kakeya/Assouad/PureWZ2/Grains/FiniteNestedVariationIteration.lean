import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.AmplifiedOneScaleCardinalityCancellation

/-!
# Finite nested iteration of one-scale plane-map variation

This is the formal bookkeeping behind WZ2 Lemma 16.  A one-scale producer is
applied successively to the current shading.  Because every producer is a
common spatial restriction, point multiplicity is preserved at surviving
points.  Previous variation estimates pass to later subshadings, while the
left and right mass factors multiply.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

theorem paper_finite_nested_variation_iteration
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading F)
    (hsourceCubical : WZ1PaperIsCubicalShading source)
    (planeMap : Point3 → Point3)
    (N : ℕ)
    (scale : ℕ → ℝ)
    (leftFactor rightFactor : ℕ → ENNReal)
    (step : ∀ k : ℕ, k < N →
      ∀ current : WZ1PaperTubeShading F,
        PaperIsSubshading current source →
        WZ1PaperIsCubicalShading current →
        (∀ p ∈ current.union,
          current.pointMultiplicity p = source.pointMultiplicity p) →
        ∃ next : WZ1PaperTubeShading F,
          PaperIsSubshading next current ∧
          WZ1PaperIsCubicalShading next ∧
          (∀ p ∈ next.union,
            next.pointMultiplicity p = current.pointMultiplicity p) ∧
          (∀ p ∈ next.union, ∀ q ∈ next.union,
            dist p q ≤ scale k →
              dist (planeMap p) (planeMap q) ≤ scale k) ∧
          leftFactor k * current.mass ≤ rightFactor k * next.mass) :
    ∃ final : WZ1PaperTubeShading F,
      PaperIsSubshading final source ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ p ∈ final.union,
        final.pointMultiplicity p = source.pointMultiplicity p) ∧
      (∀ k : ℕ, k < N →
        ∀ p ∈ final.union, ∀ q ∈ final.union,
          dist p q ≤ scale k →
            dist (planeMap p) (planeMap q) ≤ scale k) ∧
      (∏ k ∈ Finset.range N, leftFactor k) * source.mass ≤
        (∏ k ∈ Finset.range N, rightFactor k) * final.mass := by
  let P : ℕ → Prop := fun m =>
    ∃ current : WZ1PaperTubeShading F,
      PaperIsSubshading current source ∧
      WZ1PaperIsCubicalShading current ∧
      (∀ p ∈ current.union,
        current.pointMultiplicity p = source.pointMultiplicity p) ∧
      (∀ k : ℕ, k < m → k < N →
        ∀ p ∈ current.union, ∀ q ∈ current.union,
          dist p q ≤ scale k →
            dist (planeMap p) (planeMap q) ≤ scale k) ∧
      (∏ k ∈ Finset.range m, leftFactor k) * source.mass ≤
        (∏ k ∈ Finset.range m, rightFactor k) * current.mass
  have hbase : P 0 := by
    refine ⟨source, fun _ => Set.Subset.rfl, hsourceCubical, ?_, ?_, ?_⟩
    · intro p _
      rfl
    · intro k hk
      omega
    · simp
  have hnext : ∀ m : ℕ, m < N → P m → P (m + 1) := by
    intro m hm hPm
    rcases hPm with
      ⟨current, hcurrentSub, hcurrentCubical, hcurrentMultiplicity,
        hcurrentVariation, hcurrentMass⟩
    rcases step m hm current hcurrentSub hcurrentCubical hcurrentMultiplicity with
      ⟨next, hnextSub, hnextCubical, hnextMultiplicityCurrent, hnextVariation,
        hnextMass⟩
    have hnextSubSource : PaperIsSubshading next source := fun i =>
      (hnextSub i).trans (hcurrentSub i)
    have hnextMultiplicity : ∀ p ∈ next.union,
        next.pointMultiplicity p = source.pointMultiplicity p := by
      intro p hp
      have hpCurrent : p ∈ current.union := by
        rcases hp with ⟨i, hi⟩
        exact ⟨i, hnextSub i hi⟩
      exact (hnextMultiplicityCurrent p hp).trans
        (hcurrentMultiplicity p hpCurrent)
    have hvariation : ∀ k : ℕ, k < m + 1 → k < N →
        ∀ p ∈ next.union, ∀ q ∈ next.union,
          dist p q ≤ scale k →
            dist (planeMap p) (planeMap q) ≤ scale k := by
      intro k hk hNk p hp q hq hpq
      by_cases hkm : k = m
      · subst hkm
        exact hnextVariation p hp q hq hpq
      · have hkOld : k < m := by omega
        have hpCurrent : p ∈ current.union := by
          rcases hp with ⟨i, hi⟩
          exact ⟨i, hnextSub i hi⟩
        have hqCurrent : q ∈ current.union := by
          rcases hq with ⟨i, hi⟩
          exact ⟨i, hnextSub i hi⟩
        exact hcurrentVariation k hkOld hNk p hpCurrent q hqCurrent hpq
    have hmass :
        (∏ k ∈ Finset.range (m + 1), leftFactor k) * source.mass ≤
          (∏ k ∈ Finset.range (m + 1), rightFactor k) * next.mass := by
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      calc
        ((∏ k ∈ Finset.range m, leftFactor k) * leftFactor m) *
            source.mass =
            leftFactor m *
              ((∏ k ∈ Finset.range m, leftFactor k) * source.mass) := by
          ring
        _ ≤ leftFactor m *
            ((∏ k ∈ Finset.range m, rightFactor k) * current.mass) := by
          gcongr
        _ = (∏ k ∈ Finset.range m, rightFactor k) *
            (leftFactor m * current.mass) := by
          ring
        _ ≤ (∏ k ∈ Finset.range m, rightFactor k) *
            (rightFactor m * next.mass) := by
          gcongr
        _ = ((∏ k ∈ Finset.range m, rightFactor k) * rightFactor m) *
            next.mass := by
          ring
    exact ⟨next, hnextSubSource, hnextCubical, hnextMultiplicity,
      hvariation, hmass⟩
  have hinduction : ∀ m : ℕ, m ≤ N → P m := by
    intro m hm
    induction m with
    | zero => exact hbase
    | succ m ih =>
        exact hnext m (by omega) (ih (by omega))
  rcases hinduction N le_rfl with
    ⟨final, hfinalSub, hfinalCubical, hfinalMultiplicity,
      hfinalVariation, hfinalMass⟩
  exact ⟨final, hfinalSub, hfinalCubical, hfinalMultiplicity,
    (fun k hk => hfinalVariation k hk hk), hfinalMass⟩

end Kakeya.Assouad

end
