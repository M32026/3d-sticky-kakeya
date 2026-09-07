import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FixedGridDyadicSum
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62OuterBoundaryDyadicSum
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBoundaryCoefficient
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCropBoundaryGeometry

/-!
# Proposition 6.2 fixed-grid boundary mass

This sums the one-hyperplane direction-band estimate over the fixed
`rho`-grid hyperplanes and the three coordinates, as in
`WZ2_prop62.tex`, Lemma `prop62-fixed-grid`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem pureWZ2_prop62_grid_boundary_mass_cardinality
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    {C : ENNReal}
    (hcwa : WZ2PaperConvexWolffBound family C) :
    (∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            wz2PaperGridBoundaryRegion delta rho)) ≤
      (15 : ENNReal) *
        C *
        (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
        pureWZ2Prop62FixedGridPlaneConstant *
        ENNReal.ofReal (1 / rho) *
        Kakeya.realRpowENN delta 3 *
        family.enncard := by
  let boundaries := wz2PaperBoundaryIndicesInWindow rho
  let planeBound : ENNReal :=
    C *
      ((pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
        pureWZ2Prop62FixedGridPlaneConstant) *
      Kakeya.realRpowENN delta 3 *
      family.enncard
  have hpointwise :
      ∀ index : Fin family.card,
        volume
            (shading.carrier index ∩
              wz2PaperGridBoundaryRegion delta rho) ≤
          ∑ coordinate : Fin 3,
            ∑ boundary ∈ boundaries,
              volume
                (shading.carrier index ∩
                  coordinateSlab coordinate
                    ((boundary : ℝ) * rho - delta)
                    ((boundary : ℝ) * rho + delta)) := by
    intro index
    have hsubset :
        shading.carrier index ∩
            wz2PaperGridBoundaryRegion delta rho ⊆
          ⋃ coordinate : Fin 3,
            ⋃ boundary ∈ boundaries,
              (shading.carrier index ∩
                coordinateSlab coordinate
                  ((boundary : ℝ) * rho - delta)
                  ((boundary : ℝ) * rho + delta)) := by
      intro point hpoint
      rcases Set.mem_iUnion.mp hpoint.2 with
        ⟨coordinate, hcoordinate⟩
      rcases Set.mem_iUnion₂.mp hcoordinate with
        ⟨boundary, hboundary, hslab⟩
      exact Set.mem_iUnion.mpr
        ⟨coordinate,
          Set.mem_iUnion₂.mpr
            ⟨boundary, hboundary, hpoint.1, hslab⟩⟩
    calc
      volume
          (shading.carrier index ∩
            wz2PaperGridBoundaryRegion delta rho) ≤
        volume
          (⋃ coordinate : Fin 3,
            ⋃ boundary ∈ boundaries,
              (shading.carrier index ∩
                coordinateSlab coordinate
                  ((boundary : ℝ) * rho - delta)
                  ((boundary : ℝ) * rho + delta))) :=
        measure_mono hsubset
      _ ≤
          ∑ coordinate : Fin 3,
            volume
              (⋃ boundary ∈ boundaries,
                (shading.carrier index ∩
                  coordinateSlab coordinate
                    ((boundary : ℝ) * rho - delta)
                    ((boundary : ℝ) * rho + delta))) :=
        MeasureTheory.measure_iUnion_fintype_le _ _
      _ ≤
          ∑ coordinate : Fin 3,
            ∑ boundary ∈ boundaries,
              volume
                (shading.carrier index ∩
                  coordinateSlab coordinate
                    ((boundary : ℝ) * rho - delta)
                    ((boundary : ℝ) * rho + delta)) := by
        exact Finset.sum_le_sum fun coordinate _ =>
          MeasureTheory.measure_biUnion_finset_le boundaries _
  have hsum :
      (∑ index : Fin family.card,
          volume
            (shading.carrier index ∩
              wz2PaperGridBoundaryRegion delta rho)) ≤
        ∑ coordinate : Fin 3,
          ∑ boundary ∈ boundaries, planeBound := by
    calc
      (∑ index : Fin family.card,
          volume
            (shading.carrier index ∩
              wz2PaperGridBoundaryRegion delta rho)) ≤
        ∑ index : Fin family.card,
          ∑ coordinate : Fin 3,
            ∑ boundary ∈ boundaries,
              volume
                (shading.carrier index ∩
                  coordinateSlab coordinate
                    ((boundary : ℝ) * rho - delta)
                    ((boundary : ℝ) * rho + delta)) := by
          exact Finset.sum_le_sum fun index _ => hpointwise index
      _ =
        ∑ coordinate : Fin 3,
          ∑ boundary ∈ boundaries,
            ∑ index : Fin family.card,
              volume
                (shading.carrier index ∩
                  coordinateSlab coordinate
                    ((boundary : ℝ) * rho - delta)
                    ((boundary : ℝ) * rho + delta)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro coordinate hcoordinate
        rw [Finset.sum_comm]
      _ ≤
        ∑ coordinate : Fin 3,
          ∑ boundary ∈ boundaries, planeBound := by
        exact Finset.sum_le_sum fun coordinate _ =>
          Finset.sum_le_sum fun boundary _ =>
            pureWZ2_prop62_one_plane_boundary_mass
              hdelta hdeltaSmall hline shading coordinate hcwa
              (boundary := (boundary : ℝ) * rho)
  have hcardReal :=
    wz2_paper_boundary_indices_in_window_card hrho hrhoOne
  have hcardENN :
      (boundaries.card : ENNReal) ≤
        (5 : ENNReal) * ENNReal.ofReal (1 / rho) := by
    calc
      (boundaries.card : ENNReal) =
          ENNReal.ofReal (boundaries.card : ℝ) := by
        exact (ENNReal.ofReal_natCast boundaries.card).symm
      _ ≤ ENNReal.ofReal (5 / rho) := by
        exact ENNReal.ofReal_mono hcardReal
      _ = (5 : ENNReal) * ENNReal.ofReal (1 / rho) := by
        rw [show (5 : ENNReal) = ENNReal.ofReal (5 : ℝ) by norm_num]
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]
        congr 1
        ring
  calc
    (∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            wz2PaperGridBoundaryRegion delta rho)) ≤
      ∑ coordinate : Fin 3,
        ∑ boundary ∈ boundaries, planeBound := hsum
    _ =
      (3 : ENNReal) * ((boundaries.card : ENNReal) * planeBound) := by
      simp [Finset.sum_const]
    _ ≤
      (3 : ENNReal) *
        (((5 : ENNReal) * ENNReal.ofReal (1 / rho)) *
          planeBound) := by
      gcongr
    _ =
      (15 : ENNReal) *
        C *
        (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
        pureWZ2Prop62FixedGridPlaneConstant *
        ENNReal.ofReal (1 / rho) *
        Kakeya.realRpowENN delta 3 *
        family.enncard := by
      dsimp only [planeBound]
      ring

theorem pureWZ2_prop62_paper_body_mass_lower
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 12)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family) :
    family.enncard * Kakeya.realRpowENN delta 2 ≤
      (wz1PaperBodyFamily family).mass := by
  calc
    family.enncard * Kakeya.realRpowENN delta 2 =
        ∑ _index : Fin family.card,
          Kakeya.realRpowENN delta 2 := by
      simp [Kakeya.Streamlined.TubeFamily.enncard,
        Finset.sum_const]
    _ ≤
        ∑ index : Fin family.card,
          volume (wz1PaperTubeCarrier (family.tube index)) := by
      exact Finset.sum_le_sum fun index _ => by
        simpa [Kakeya.realRpowENN, Real.rpow_two] using
          (canonical_volume_lower hdelta).trans
            (wz2PaperTubeCarrier_volume_lower
              hdelta hdeltaSmall
              (family.tube index) (hline index))
    _ = (wz1PaperBodyFamily family).mass := rfl

theorem pureWZ2_prop62_grid_boundary_mass
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    {C : ENNReal}
    (hcwa : WZ2PaperConvexWolffBound family C) :
    (∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            wz2PaperGridBoundaryRegion delta rho)) ≤
      (15 : ENNReal) *
        C *
        (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
        pureWZ2Prop62FixedGridPlaneConstant *
        ENNReal.ofReal (delta / rho) *
        (wz1PaperBodyFamily family).mass := by
  have hcardinality :=
    pureWZ2_prop62_grid_boundary_mass_cardinality
      hdelta hdeltaSmall hrho hrhoOne hline shading hcwa
  have hbody :=
    pureWZ2_prop62_paper_body_mass_lower
      hdelta (hdeltaSmall.trans (by norm_num)) hline
  have hdeltaCube :
      Kakeya.realRpowENN delta 3 =
        ENNReal.ofReal delta * Kakeya.realRpowENN delta 2 := by
    simp [Kakeya.realRpowENN, Real.rpow_natCast,
      ENNReal.ofReal_pow hdelta.le]
    ring
  have hratio :
      ENNReal.ofReal (1 / rho) * ENNReal.ofReal delta =
        ENNReal.ofReal (delta / rho) := by
    rw [← ENNReal.ofReal_mul]
    · congr 1
      ring
    · positivity
  calc
    (∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            wz2PaperGridBoundaryRegion delta rho)) ≤
      (15 : ENNReal) *
        C *
        (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
        pureWZ2Prop62FixedGridPlaneConstant *
        ENNReal.ofReal (1 / rho) *
        Kakeya.realRpowENN delta 3 *
        family.enncard := hcardinality
    _ =
      (15 : ENNReal) *
        C *
        (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
        pureWZ2Prop62FixedGridPlaneConstant *
        ENNReal.ofReal (delta / rho) *
        (family.enncard * Kakeya.realRpowENN delta 2) := by
      rw [hdeltaCube]
      calc
        (15 : ENNReal) *
              C *
              (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
              pureWZ2Prop62FixedGridPlaneConstant *
              ENNReal.ofReal (1 / rho) *
              (ENNReal.ofReal delta *
                Kakeya.realRpowENN delta 2) *
              family.enncard =
            (15 : ENNReal) *
              C *
              (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
              pureWZ2Prop62FixedGridPlaneConstant *
              (ENNReal.ofReal (1 / rho) * ENNReal.ofReal delta) *
              (family.enncard * Kakeya.realRpowENN delta 2) := by
          ring
        _ =
            (15 : ENNReal) *
              C *
              (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
              pureWZ2Prop62FixedGridPlaneConstant *
              ENNReal.ofReal (delta / rho) *
              (family.enncard * Kakeya.realRpowENN delta 2) := by
          rw [hratio]
    _ ≤
      (15 : ENNReal) *
        C *
        (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
        pureWZ2Prop62FixedGridPlaneConstant *
        ENNReal.ofReal (delta / rho) *
        (wz1PaperBodyFamily family).mass := by
      gcongr

theorem pureWZ2_prop62_outer_boundary_mass_cardinality
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    {C : ENNReal}
    (hcwa : WZ2PaperConvexWolffBound family C) :
    (∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            wz2PaperCropBoundaryRegion rho)) ≤
      6 *
        C *
        (pureWZ2Prop62OuterDirectionLevelCount rho : ENNReal) *
        pureWZ2Prop62OuterFaceConstant *
        ENNReal.ofReal rho *
        Kakeya.realRpowENN delta 2 *
        family.enncard := by
  let positiveFace : Fin 3 → Set Point3 := fun coordinate =>
    coordinateSlab coordinate (1 - rho) (1 + rho)
  let negativeFace : Fin 3 → Set Point3 := fun coordinate =>
    coordinateSlab coordinate (-1 - rho) (-1 + rho)
  let faceBound : ENNReal :=
    C *
      ((pureWZ2Prop62OuterDirectionLevelCount rho : ENNReal) *
        pureWZ2Prop62OuterFaceConstant) *
      ENNReal.ofReal rho *
      Kakeya.realRpowENN delta 2 *
      family.enncard
  have hsubset :
      wz2PaperCropBoundaryRegion rho ⊆
        (⋃ coordinate : Fin 3, positiveFace coordinate) ∪
          ⋃ coordinate : Fin 3, negativeFace coordinate := by
    intro point hpoint
    rcases hpoint with ⟨hbox, coordinate, hboundary⟩
    have hcoordinate : |point coordinate| ≤ 1 := by
      have h := hbox
      simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at h
      norm_num at h
      fin_cases coordinate <;> tauto
    by_cases hnonnegative : 0 ≤ point coordinate
    · apply Or.inl
      apply Set.mem_iUnion.mpr
      refine ⟨coordinate, ?_⟩
      change 1 - rho ≤ point coordinate ∧
        point coordinate ≤ 1 + rho
      rw [abs_of_nonneg hnonnegative] at hboundary hcoordinate
      constructor <;> linarith
    · apply Or.inr
      apply Set.mem_iUnion.mpr
      refine ⟨coordinate, ?_⟩
      change -1 - rho ≤ point coordinate ∧
        point coordinate ≤ -1 + rho
      have hnegative : point coordinate < 0 :=
        lt_of_not_ge hnonnegative
      rw [abs_of_neg hnegative] at hboundary hcoordinate
      constructor <;> linarith
  have hpointwise :
      ∀ index : Fin family.card,
        volume
            (shading.carrier index ∩
              wz2PaperCropBoundaryRegion rho) ≤
          (∑ coordinate : Fin 3,
              volume
                (shading.carrier index ∩
                  positiveFace coordinate)) +
            ∑ coordinate : Fin 3,
              volume
                (shading.carrier index ∩
                  negativeFace coordinate) := by
    intro index
    have hset :
        shading.carrier index ∩
            wz2PaperCropBoundaryRegion rho ⊆
          (⋃ coordinate : Fin 3,
              shading.carrier index ∩ positiveFace coordinate) ∪
            ⋃ coordinate : Fin 3,
              shading.carrier index ∩ negativeFace coordinate := by
      intro point hpoint
      rcases hsubset hpoint.2 with hpositive | hnegative
      · rcases Set.mem_iUnion.mp hpositive with
          ⟨coordinate, hcoordinate⟩
        exact Or.inl <| Set.mem_iUnion.mpr
          ⟨coordinate, hpoint.1, hcoordinate⟩
      · rcases Set.mem_iUnion.mp hnegative with
          ⟨coordinate, hcoordinate⟩
        exact Or.inr <| Set.mem_iUnion.mpr
          ⟨coordinate, hpoint.1, hcoordinate⟩
    calc
      volume
          (shading.carrier index ∩
            wz2PaperCropBoundaryRegion rho) ≤
        volume
          ((⋃ coordinate : Fin 3,
              shading.carrier index ∩ positiveFace coordinate) ∪
            ⋃ coordinate : Fin 3,
              shading.carrier index ∩ negativeFace coordinate) :=
        measure_mono hset
      _ ≤
          volume
              (⋃ coordinate : Fin 3,
                shading.carrier index ∩ positiveFace coordinate) +
            volume
              (⋃ coordinate : Fin 3,
                shading.carrier index ∩ negativeFace coordinate) :=
        measure_union_le _ _
      _ ≤
          (∑ coordinate : Fin 3,
              volume
                (shading.carrier index ∩
                  positiveFace coordinate)) +
            ∑ coordinate : Fin 3,
              volume
                (shading.carrier index ∩
                  negativeFace coordinate) := by
        gcongr
        · exact MeasureTheory.measure_iUnion_fintype_le _ _
        · exact MeasureTheory.measure_iUnion_fintype_le _ _
  have hpositive :
      ∀ coordinate : Fin 3,
        (∑ index : Fin family.card,
            volume
              (shading.carrier index ∩
                positiveFace coordinate)) ≤ faceBound := by
    intro coordinate
    simpa only [positiveFace, faceBound] using
      pureWZ2_prop62_outer_face_boundary_mass
        hdelta hdeltaSmall hrho hrhoOne hdeltaRho
        hline shading coordinate hcwa (boundary := 1)
  have hnegative :
      ∀ coordinate : Fin 3,
        (∑ index : Fin family.card,
            volume
              (shading.carrier index ∩
                negativeFace coordinate)) ≤ faceBound := by
    intro coordinate
    simpa only [negativeFace, faceBound] using
      pureWZ2_prop62_outer_face_boundary_mass
        hdelta hdeltaSmall hrho hrhoOne hdeltaRho
        hline shading coordinate hcwa (boundary := -1)
  calc
    (∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            wz2PaperCropBoundaryRegion rho)) ≤
      ∑ index : Fin family.card,
        ((∑ coordinate : Fin 3,
            volume
              (shading.carrier index ∩
                positiveFace coordinate)) +
          ∑ coordinate : Fin 3,
            volume
              (shading.carrier index ∩
                negativeFace coordinate)) := by
      exact Finset.sum_le_sum fun index _ => hpointwise index
    _ =
      (∑ coordinate : Fin 3,
          ∑ index : Fin family.card,
            volume
              (shading.carrier index ∩
                positiveFace coordinate)) +
        ∑ coordinate : Fin 3,
          ∑ index : Fin family.card,
            volume
              (shading.carrier index ∩
                negativeFace coordinate) := by
      rw [Finset.sum_add_distrib]
      congr 1 <;> exact Finset.sum_comm
    _ ≤
      (∑ _coordinate : Fin 3, faceBound) +
        ∑ _coordinate : Fin 3, faceBound := by
      exact add_le_add
        (Finset.sum_le_sum fun coordinate _ => hpositive coordinate)
        (Finset.sum_le_sum fun coordinate _ => hnegative coordinate)
    _ = 6 * faceBound := by
      simp [Finset.sum_const]
      ring
    _ =
      6 *
        C *
        (pureWZ2Prop62OuterDirectionLevelCount rho : ENNReal) *
        pureWZ2Prop62OuterFaceConstant *
        ENNReal.ofReal rho *
        Kakeya.realRpowENN delta 2 *
        family.enncard := by
      dsimp only [faceBound]
      ring

theorem pureWZ2_prop62_outer_boundary_mass
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    {C : ENNReal}
    (hcwa : WZ2PaperConvexWolffBound family C) :
    (∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            wz2PaperCropBoundaryRegion rho)) ≤
      6 *
        C *
        (pureWZ2Prop62OuterDirectionLevelCount rho : ENNReal) *
        pureWZ2Prop62OuterFaceConstant *
        ENNReal.ofReal rho *
        (wz1PaperBodyFamily family).mass := by
  have hcardinality :=
    pureWZ2_prop62_outer_boundary_mass_cardinality
      hdelta hdeltaSmall hrho hrhoOne hdeltaRho
      hline shading hcwa
  have hbody :=
    pureWZ2_prop62_paper_body_mass_lower
      hdelta (hdeltaSmall.trans (by norm_num)) hline
  calc
    (∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            wz2PaperCropBoundaryRegion rho)) ≤
      6 *
        C *
        (pureWZ2Prop62OuterDirectionLevelCount rho : ENNReal) *
        pureWZ2Prop62OuterFaceConstant *
        ENNReal.ofReal rho *
        Kakeya.realRpowENN delta 2 *
        family.enncard := hcardinality
    _ =
      6 *
        C *
        (pureWZ2Prop62OuterDirectionLevelCount rho : ENNReal) *
        pureWZ2Prop62OuterFaceConstant *
        ENNReal.ofReal rho *
        (family.enncard * Kakeya.realRpowENN delta 2) := by ring
    _ ≤
      6 *
        C *
        (pureWZ2Prop62OuterDirectionLevelCount rho : ENNReal) *
        pureWZ2Prop62OuterFaceConstant *
        ENNReal.ofReal rho *
        (wz1PaperBodyFamily family).mass := by
      gcongr

end Kakeya.Assouad

end
