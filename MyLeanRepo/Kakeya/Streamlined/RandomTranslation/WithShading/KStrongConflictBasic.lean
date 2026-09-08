import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.StrongNonDistinctDilatedContainment
import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.RigidMotionNormalizationSelection.GeometryHelpers
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CapsuleBounds
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TranslateUniformStructure
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Lightweight K-strong conflict geometry

This module contains the conflict graph and the support-free containment
geometry.  It deliberately imports neither of the two historical
`volume_dilatedTubeCarrier` implementations.
-/

open scoped Classical

noncomputable section

open MeasureTheory Metric SimpleGraph Finset
open Kakeya.Streamlined
open Kakeya.Streamlined.GeometricLemmas
open Kakeya.Streamlined.RandomTranslation

namespace Kakeya.Streamlined.WithShading

/-- K-strong ED conflict graph on a tube family. -/
def kStrongConflictGraph {delta : ℝ} (G : TubeFamily delta)
    (V K : ENNReal) : SimpleGraph (Fin G.card) :=
  { Adj := fun v w => v ≠ w ∧
      volume ((G.tube v).carrier ∩ (G.tube w).carrier) > V / K
    symm := ⟨fun {v w} h =>
      ⟨h.1.symm, by simpa [Set.inter_comm] using h.2⟩⟩ }

/-- Dilated tube carrier commutes with translation. -/
lemma dilatedTubeCarrier_translate {delta : ℝ} {A : ℝ}
    (hA : 0 ≤ A) (T : Kakeya.DeltaTube delta) (v : Point3) :
    dilatedTubeCarrier A (translateTube T v) =
      (fun x => x + v) '' dilatedTubeCarrier A T := by
  rw [Kakeya.Streamlined.GeneralizedFrostman.dilatedTubeCarrier_translate]
  rfl

/-- Overlapping tubes have midpoint distance at most three. -/
lemma overlapping_tubes_midpoint_dist_le_3
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    {T1 T2 : Kakeya.DeltaTube delta}
    (hnonempty : (T1.carrier ∩ T2.carrier).Nonempty) :
    dist (tubeMidpoint T1) (tubeMidpoint T2) ≤ 3 := by
  rcases hnonempty with ⟨p, hp1, hp2⟩
  have h1 : dist p (tubeMidpoint T1) ≤ 1 / 2 + delta :=
    Kakeya.Streamlined.GeneralizedFrostman.tube_point_dist_to_midpoint
      hdelta.le T1 p hp1
  have h2 : dist p (tubeMidpoint T2) ≤ 1 / 2 + delta :=
    Kakeya.Streamlined.GeneralizedFrostman.tube_point_dist_to_midpoint
      hdelta.le T2 p hp2
  calc
    dist (tubeMidpoint T1) (tubeMidpoint T2) ≤
        dist (tubeMidpoint T1) p + dist p (tubeMidpoint T2) :=
      dist_triangle _ _ _
    _ = dist p (tubeMidpoint T1) + dist p (tubeMidpoint T2) := by
      rw [dist_comm (tubeMidpoint T1) p]
    _ ≤ (1 / 2 + delta) + (1 / 2 + delta) := by gcongr
    _ ≤ 3 := by linarith

/-- K-strong containment after translating to bounded midpoint geometry. -/
lemma strong_containment_via_translation
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    {T1 T2 : Kakeya.DeltaTube delta} {K : ℝ} (hK : 2 ≤ K)
    (hoverlap : volume (T1.carrier ∩ T2.carrier) >
        T1.volume / ENNReal.ofReal K) :
    T1.carrier ⊆ dilatedTubeCarrier (1000 * K) T2 := by
  let m1 := tubeMidpoint T1
  let m2 := tubeMidpoint T2
  let v : Point3 := -m1
  let T1' := translateTube T1 v
  let T2' := translateTube T2 v
  have hmid :
      ∀ T : Kakeya.DeltaTube delta,
        tubeMidpoint (translateTube T v) = tubeMidpoint T + v := by
    intro T
    simp [tubeMidpoint, translateTube] <;> abel
  have hm1 : tubeMidpoint T1' = 0 := by
    rw [hmid T1]
    simp [v, m1]
  have hm2 : tubeMidpoint T2' = m2 - m1 := by
    rw [hmid T2]
    simp [v, m1, m2] <;> abel
  let V := Kakeya.deltaTubeVolume delta
  have hVpos : 0 < V := by
    have hlower :
        V ≥ ENNReal.ofReal
          (Real.pi * delta ^ 2 +
            (4 / 3 : ℝ) * Real.pi * delta ^ 3) :=
      capsule_volume_lower delta hdelta
    have hreal :
        0 < Real.pi * delta ^ 2 +
          (4 / 3 : ℝ) * Real.pi * delta ^ 3 := by
      positivity
    exact (ENNReal.ofReal_pos.mpr hreal).trans_le hlower
  have hvol1 : T1.volume = V :=
    tube_volume_eq T1
      ⟨0, EuclideanSpace.single 0 1, by simp⟩
  have hinterpos : 0 < volume (T1.carrier ∩ T2.carrier) := by
    have hdenom : 0 < T1.volume / ENNReal.ofReal K := by
      rw [hvol1]
      exact ENNReal.div_pos hVpos.ne' ENNReal.ofReal_ne_top
    exact hdenom.trans hoverlap
  have hinter : (T1.carrier ∩ T2.carrier).Nonempty := by
    by_contra h
    have hempty : T1.carrier ∩ T2.carrier = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using h
    rw [hempty] at hinterpos
    simp at hinterpos
  have hdist : dist m1 m2 ≤ 3 :=
    overlapping_tubes_midpoint_dist_le_3
      hdelta hdelta_one hinter
  have hnorm1 : ‖tubeMidpoint T1'‖ ≤ 3 := by
    rw [hm1]
    norm_num
  have hnorm2 : ‖tubeMidpoint T2'‖ ≤ 3 := by
    rw [hm2]
    calc
      ‖m2 - m1‖ = dist m1 m2 := by
        rw [← dist_eq_norm, dist_comm]
      _ ≤ 3 := hdist
  have hcar1 :
      T1'.carrier = (fun x => x + v) '' T1.carrier :=
    translateTube_carrier T1 v
  have hcar2 :
      T2'.carrier = (fun x => x + v) '' T2.carrier :=
    translateTube_carrier T2 v
  have hvol1' : T1'.volume = T1.volume :=
    translateTube_volume T1 v
  have hintertrans :
      T1'.carrier ∩ T2'.carrier =
        (fun x => x + v) '' (T1.carrier ∩ T2.carrier) := by
    rw [hcar1, hcar2]
    ext x
    simp
    <;> constructor <;> rintro ⟨y, hy, rfl⟩ <;>
      exact ⟨y, hy, rfl⟩
  have hmeas : MeasurableSet (T1.carrier ∩ T2.carrier) :=
    Metric.isClosed_cthickening.measurableSet.inter
      Metric.isClosed_cthickening.measurableSet
  have hvoltrans :
      volume ((fun x => x + v) '' (T1.carrier ∩ T2.carrier)) =
        volume (T1.carrier ∩ T2.carrier) :=
    volume_translateSet hmeas v
  have hoverlap' :
      volume (T1'.carrier ∩ T2'.carrier) >
        T1'.volume / ENNReal.ofReal K := by
    rw [hintertrans, hvoltrans, hvol1']
    exact hoverlap
  have hcontain :
      T1'.carrier ⊆ dilatedTubeCarrier (1000 * K) T2' :=
    strong_non_distinct_dilated_containment_lemma
      hdelta hdelta_one T1' T2' hnorm1 hnorm2 hK hoverlap'
  have hdil :
      dilatedTubeCarrier (1000 * K) T2' =
        (fun x => x + v) ''
          dilatedTubeCarrier (1000 * K) T2 :=
    dilatedTubeCarrier_translate (by positivity) T2 v
  rw [hdil, hcar1] at hcontain
  intro x hx
  have hx' : x + v ∈ (fun x => x + v) '' T1.carrier :=
    ⟨x, hx, by abel⟩
  rcases hcontain hx' with ⟨y, hy, hxy⟩
  have hyx : y = x := by simpa [add_left_inj] using hxy
  rwa [hyx] at hy

end Kakeya.Streamlined.WithShading

end
