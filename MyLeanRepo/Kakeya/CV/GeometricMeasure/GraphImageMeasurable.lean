import MyLeanRepo.Kakeya.CV.GeometricMeasure.GraphPullbackMeasure
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Measurability of a graph image on a measurable domain

A function continuous on a measurable subset of a Euclidean space defines a
measurable graph image over that subset.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.CV

/-- The graph of a function continuous on a measurable set is measurable. -/
lemma graphMap_image_measurable_of_continuousOn
    {U : Set R2} {g : R2 → ℝ}
    (hU : MeasurableSet U) (hg : ContinuousOn g U) :
    MeasurableSet (graphMap g '' U) := by
  letI := hU.standardBorel
  let graphU : U → Point 3 := fun x => graphMap g (x : R2)
  have hgraph_contOn : ContinuousOn (graphMap g) U := by
    have hpi :
        ContinuousOn
          (fun x : R2 => (![x 0, x 1, g x] : Fin 3 → ℝ)) U := by
      rw [continuousOn_pi]
      intro i
      fin_cases i
      · exact
          (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).continuousOn
      · exact
          (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).continuousOn
      · exact hg
    exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp_continuousOn
      hpi
  have hgraphU_cont : Continuous graphU :=
    continuousOn_iff_continuous_restrict.mp hgraph_contOn
  have hgraphU_inj : Function.Injective graphU := by
    intro x y hxy
    exact Subtype.ext ((graphMap_injective g) hxy)
  have h_emb : MeasurableEmbedding graphU :=
    hgraphU_cont.measurable.measurableEmbedding hgraphU_inj
  have h_image :
      graphU '' Set.univ = graphMap g '' U := by
    ext z
    constructor
    · rintro ⟨x, -, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
  rw [← h_image]
  exact h_emb.measurableSet_image.mpr MeasurableSet.univ

end Kakeya.CV
