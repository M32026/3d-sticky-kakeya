module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.GeneralLineEDAnalyticBridgeW95

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

open RevisedLiteralProfileInterfaceFormalizerW87

/-- A genuine positive-mass one-layer representative selection.  The witness
is the same input family and the loss is the existing line-parameter packing
constant; no raw-tree fields are assumed. -/
theorem exists_weighted_line_selection_w102
    {delta : NNReal} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {iota : Type uI} [DecidableEq iota]
    (F : Finset iota) (Y : iota → ShadedTube delta E)
    (hball : ∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1)
    (Cbase : NNReal)
    (hline : lineEssentiallyDistinctW94 F (fun i => (Y i).toTube) Cbase)
    (hmass : 0 < ∑ i ∈ F, volume (Y i).shade)
    (hCbase : 1 ≤ Cbase) :
    ∃ (M : Nat) (q : Finset iota),
      1 ≤ M ∧ q ⊆ F ∧ q.Nonempty ∧
      (q : Set iota).Pairwise
        (fun i j => IsEssentiallyDistinct (Y i).carrier (Y j).carrier) ∧
      (∑ i ∈ F, volume (Y i).shade) <=
        (M : ENNReal) * (∑ i ∈ q, volume (Y i).shade) := by
  have hF : F.Nonempty := by
    by_contra hF
    simp only [Finset.not_nonempty_iff_eq_empty.mp hF, Finset.sum_empty,
      lt_self_iff_false] at hmass
  have hfloor : 1 ≤ Nat.floor (Cbase : Real) := by
    apply (Nat.le_floor_iff Cbase.coe_nonneg).mpr
    exact_mod_cast hCbase
  have hcenter : ∀ i ∈ F, ‖(Y i).center‖ ≤ (1 : Real) := by
    intro i hi
    have hm := Tube.norm_midpoint_le_of_subset_ball hdelta (Y i).toTube
      (hball i hi)
    have heq : (Y i).center = (Y i).toTube.midpoint := by
      change midpoint Real (Y i).x (Y i).y = (1 / 2 : Real) •
        ((Y i).x + (Y i).y)
      rw [midpoint_eq_smul_add]
      norm_num
    rw [heq]
    exact hm
  have hline' : VeryNotSticky.IsLineEssDistinct (Nat.floor (Cbase : Real)) F
      (fun i => (Y i).toTube) := by
    exact (pointwise_lineED_iff_library_floor_w95 F
      (fun i => (Y i).toTube) Cbase).mp hline
  let K0 : ConvexSpaceBody E := ConvexSpaceBody.closedUnitBall
  have hcontained : ∀ i ∈ F, (Y i).toConvexSpaceBody ≤ K0 := by
    intro i hi
    exact SetLike.coe_subset_coe.mpr (hball i hi)
  obtain ⟨q, hqF, hqne, hqED, hqmass, hqcard, hqfull, hqCF, hqmax, hqmu⟩ :=
    exists_pairwise_lineED_paid_w95 hdelta hdelta1 F Y hF 1 (by norm_num)
      hcenter (Nat.floor (Cbase : Real)) hfloor hline' K0 hcontained hmass
  refine ⟨lineSelectionMultiplicityW95 (Module.finrank Real E) 1
      (Nat.floor (Cbase : Real)), q, ?_, hqF, hqne, hqED, hqmass⟩
  exact Nat.mul_pos
    (by
      apply Nat.ceil_pos.mpr
      have hK : 1 ≤ Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank Real E) :=
        (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C _).le
      positivity)
    (by omega)

end
end Kakeya.ml1Boot.TrialRestartW94
