import MyLeanRepo.Kakeya.Assouad.Targets.CompactTubeTwistedProjectionArea.CoordEquiv
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SameHeightDiameter

/-!
# Same-height fiber diameter inside a vertical-chart tube
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

lemma tube_y_diameter_bound
    {δ : ℝ} (hδ : 0 < δ)
    {T : Kakeya.DeltaTube δ}
    (hdir : (1 / 2 : ℝ) ≤ |T.direction (2 : Fin 3)|)
    {A : Set Point3} (hA : A ⊆ T.carrier) :
    ∀ z y1 y2 : ℝ,
      (∃ x1 x2 : ℝ,
        (z, (x1, y1)) ∈ coordEquiv3 '' A ∧
        (z, (x2, y2)) ∈ coordEquiv3 '' A) →
      |y1 - y2| ≤ 6 * δ := by
  intro z y1 y2 h
  rcases h with
    ⟨x1, x2, ⟨p1, hp1, hcoord1⟩, ⟨p2, hp2, hcoord2⟩⟩
  have hp1z : p1 (2 : Fin 3) = z := by
    simpa [coordEquiv3, Prod.ext_iff] using
      congr_arg Prod.fst hcoord1
  have hp2z : p2 (2 : Fin 3) = z := by
    simpa [coordEquiv3, Prod.ext_iff] using
      congr_arg Prod.fst hcoord2
  have hp1y : p1 (1 : Fin 3) = y1 := by
    have hsecond := congr_arg Prod.snd hcoord1
    simpa [coordEquiv3, Prod.ext_iff] using
      congr_arg Prod.snd hsecond
  have hp2y : p2 (1 : Fin 3) = y2 := by
    have hsecond := congr_arg Prod.snd hcoord2
    simpa [coordEquiv3, Prod.ext_iff] using
      congr_arg Prod.snd hsecond
  let F : Kakeya.Streamlined.TubeFamily δ :=
    { card := 1
      tube := fun _ => T }
  have hvert : IsInVerticalChart F := by
    intro _
    exact hdir
  let i : Fin F.card := 0
  let axisPoint : Point3 :=
    point3 ((tubeParams i).a + (tubeParams i).c * z)
      ((tubeParams i).b + (tubeParams i).d * z) z
  have hdist1 : ‖p1 - axisPoint‖ ≤ 3 * δ := by
    exact tubeCarrier_axisDistance hδ.le hvert i p1 (hA hp1) z hp1z
  have hdist2 : ‖p2 - axisPoint‖ ≤ 3 * δ := by
    exact tubeCarrier_axisDistance hδ.le hvert i p2 (hA hp2) z hp2z
  have hy1 : |p1 1 - axisPoint 1| ≤ 3 * δ := by
    exact
      (euclidean_coord_le_norm (p1 - axisPoint) 1).trans hdist1
  have hy2 : |p2 1 - axisPoint 1| ≤ 3 * δ := by
    exact
      (euclidean_coord_le_norm (p2 - axisPoint) 1).trans hdist2
  rw [hp1y, hp2y] at *
  calc
    |y1 - y2|
        = |(y1 - axisPoint 1) + (axisPoint 1 - y2)| := by ring_nf
    _ ≤ |y1 - axisPoint 1| + |axisPoint 1 - y2| := abs_add_le _ _
    _ = |y1 - axisPoint 1| + |y2 - axisPoint 1| := by
      rw [abs_sub_comm (axisPoint 1) y2]
    _ ≤ 3 * δ + 3 * δ := add_le_add hy1 hy2
    _ = 6 * δ := by ring

end Kakeya.Assouad
