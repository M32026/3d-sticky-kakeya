import MyLeanRepo.Kakeya.CV.Statements
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Geometry.Euclidean.Volume.Measure

namespace Kakeya.CV

lemma volume_eq_smul_hausdorff {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] :
    ∃ (c : ENNReal), (MeasureTheory.volume : MeasureTheory.Measure F) =
      c • MeasureTheory.Measure.hausdorffMeasure (↑(Module.finrank ℝ F)) := by
  let d := Module.finrank ℝ F
  have h1 : (MeasureTheory.volume : MeasureTheory.Measure F) =
      (MeasureTheory.Measure.euclideanHausdorffMeasure d : MeasureTheory.Measure F) :=
    (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := F)).symm
  have h2 : (MeasureTheory.Measure.euclideanHausdorffMeasure d : MeasureTheory.Measure F) =
      (MeasureTheory.Measure.addHaarScalarFactor
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))
        (MeasureTheory.Measure.hausdorffMeasure (↑d)) : ENNReal) •
      MeasureTheory.Measure.hausdorffMeasure (↑d) := by
    exact MeasureTheory.Measure.euclideanHausdorffMeasure_def (d := d)
  exact ⟨_, h1.trans h2⟩

theorem measure_zero_range_of_finrank_lt {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {f : E → F} (hf : ContDiff ℝ 1 f)
    (h : Module.finrank ℝ E < Module.finrank ℝ F) :
    MeasureTheory.volume (Set.range f) = 0 := by
  have hdim : dimH (Set.range f) ≤ ↑(Module.finrank ℝ E) :=
    hf.dimH_range_le
  let d : NNReal := ↑(Module.finrank ℝ F)
  have hlt : dimH (Set.range f) < (d : ENNReal) := by
    exact hdim.trans_lt (Nat.cast_lt.mpr h)
  have hH0 : MeasureTheory.Measure.hausdorffMeasure (↑d) (Set.range f) = 0 :=
    hausdorffMeasure_of_dimH_lt hlt
  rcases volume_eq_smul_hausdorff (F := F) with ⟨c, hc⟩
  have hvol0 : MeasureTheory.volume (Set.range f) = 0 := by
    rw [hc, MeasureTheory.Measure.smul_apply]
    have hH0' : MeasureTheory.Measure.hausdorffMeasure (↑(Module.finrank ℝ F)) (Set.range f) = 0 := by
      exact_mod_cast hH0
    rw [hH0'] <;> simp
  exact hvol0

end Kakeya.CV
