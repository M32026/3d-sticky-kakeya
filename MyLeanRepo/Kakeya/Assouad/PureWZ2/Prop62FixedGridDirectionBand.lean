import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBoundarySlowTubes
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoordinateSlabVolume
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.DyadicPigeonhole

/-!
# Proposition 6.2 fixed-grid boundary: one direction band

This is the single-band estimate in the proof of
`WZ2_prop62.tex`, Lemma `prop62-fixed-grid`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

def pureWZ2Prop62DirectionBandIndices
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (coordinate : Fin 3)
    (boundary scale : ℝ) : Finset (Fin family.card) :=
  Finset.univ.filter fun index =>
    scale ≤ |wz1PaperDirection (family.tube index) coordinate| ∧
      |wz1PaperDirection (family.tube index) coordinate| ≤ 2 * scale ∧
      (wz1PaperTubeCarrier (family.tube index) ∩
        coordinateSlab coordinate
          (boundary - delta) (boundary + delta)).Nonempty

theorem pureWZ2_prop62_direction_band_boundary_mass
    {delta scale boundary : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hscale : 0 < scale)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    (coordinate : Fin 3)
    {C : ENNReal}
    (hcwa : WZ2PaperConvexWolffBound family C) :
    let band :=
      pureWZ2Prop62DirectionBandIndices
        family coordinate boundary scale
    (∑ index ∈ band,
        volume
          (shading.carrier index ∩
            coordinateSlab coordinate
              (boundary - delta) (boundary + delta))) ≤
      (C *
          ENNReal.ofReal
            (16 * (8 * scale + 49 * delta)) *
          family.enncard) *
        (4 *
          ENNReal.ofReal
            (Real.pi * (24 * delta) ^ 2 *
              ((50 * delta) / scale + 48 * delta))) := by
  dsimp only
  let band :=
    pureWZ2Prop62DirectionBandIndices
      family coordinate boundary scale
  let container :=
    wz2PaperBoundaryContainer coordinate boundary
      (8 * scale + 49 * delta)
  have hwidthPos : 0 < 8 * scale + 49 * delta := by positivity
  have hcontained :
      ∀ index ∈ band,
        wz1PaperTubeCarrier (family.tube index) ⊆ container := by
    intro index hindex
    have hdata :
        scale ≤
            |wz1PaperDirection (family.tube index) coordinate| ∧
          |wz1PaperDirection (family.tube index) coordinate| ≤
              2 * scale ∧
          (wz1PaperTubeCarrier (family.tube index) ∩
            coordinateSlab coordinate
              (boundary - delta) (boundary + delta)).Nonempty :=
      (Finset.mem_filter.mp hindex).2
    have hraw :=
      wz2_paper_slow_boundary_tube_contained
        hdelta (by positivity : 0 ≤ 2 * scale)
        (family.tube index) (hline index) coordinate
        hdata.2.1 hdata.2.2
    change
      wz1PaperTubeCarrier (family.tube index) ⊆
        wz2PaperBoundaryContainer coordinate boundary
          (8 * scale + 49 * delta)
    simpa only [show
      4 * (2 * scale) + 49 * delta =
        8 * scale + 49 * delta by ring] using hraw
  have hbandCard :
      (band.card : ENNReal) ≤
        C *
          ENNReal.ofReal
            (16 * (8 * scale + 49 * delta)) *
          family.enncard := by
    have hcount :=
      hcwa container
        (convex_wz2PaperBoundaryContainer coordinate boundary
          (8 * scale + 49 * delta))
    have hsubset :
        band ⊆
          (Finset.univ : Finset (Fin family.card)).filter fun index =>
            wz1PaperTubeCarrier (family.tube index) ⊆ container := by
      intro index hindex
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hcontained index hindex⟩
    have hcard :
        (band.card : ENNReal) ≤
          (((Finset.univ : Finset (Fin family.card)).filter fun index =>
            wz1PaperTubeCarrier (family.tube index) ⊆ container).card :
              ENNReal) := by
      exact_mod_cast Finset.card_le_card hsubset
    have hvolume :
        volume container ≤
          ENNReal.ofReal
            (16 * (8 * scale + 49 * delta)) :=
      volume_wz2PaperBoundaryContainer_le coordinate boundary
        (8 * scale + 49 * delta) hwidthPos
    exact hcard.trans <| hcount.trans <| by
      gcongr
  let tubeBound : ENNReal :=
    4 *
      ENNReal.ofReal
        (Real.pi * (24 * delta) ^ 2 *
          ((50 * delta) / scale + 48 * delta))
  have htube :
      ∀ index ∈ band,
        volume
            (shading.carrier index ∩
              coordinateSlab coordinate
                (boundary - delta) (boundary + delta)) ≤
          tubeBound := by
    intro index hindex
    have hdirection :
        scale ≤
          |wz1PaperDirection (family.tube index) coordinate| :=
      ((Finset.mem_filter.mp hindex).2).1
    have hsubset :
        shading.carrier index ∩
            coordinateSlab coordinate
              (boundary - delta) (boundary + delta) ⊆
          wz1PaperTubeCarrier (family.tube index) ∩
            coordinateSlab coordinate
              (boundary - delta) (boundary + delta) := by
      intro point hpoint
      exact ⟨shading.subset_body index hpoint.1, hpoint.2⟩
    have hslab :=
      wz2_paper_tube_coordinate_slab_volume
        hdelta hdeltaSmall (by linarith) hscale
        (family.tube index) (hline index) coordinate hdirection
        (a := boundary - delta) (b := boundary + delta)
    have hlength :
        (boundary + delta - (boundary - delta) +
              2 * (24 * delta)) /
              scale +
            2 * (24 * delta) =
          (50 * delta) / scale + 48 * delta := by
      field_simp [hscale.ne']
      ring
    rw [hlength] at hslab
    apply (measure_mono hsubset).trans
    simpa only [tubeBound] using hslab
  calc
    (∑ index ∈ band,
        volume
          (shading.carrier index ∩
            coordinateSlab coordinate
              (boundary - delta) (boundary + delta)))
        ≤ ∑ _index ∈ band, tubeBound := by
          exact Finset.sum_le_sum fun index hindex =>
            htube index hindex
    _ = (band.card : ENNReal) * tubeBound := by
      simp [Finset.sum_const]
    _ ≤
        (C *
            ENNReal.ofReal
              (16 * (8 * scale + 49 * delta)) *
            family.enncard) *
          tubeBound := by
      gcongr
    _ =
        (C *
            ENNReal.ofReal
              (16 * (8 * scale + 49 * delta)) *
            family.enncard) *
          (4 *
            ENNReal.ofReal
              (Real.pi * (24 * delta) ^ 2 *
                ((50 * delta) / scale + 48 * delta))) := rfl

end Kakeya.Assouad

end
