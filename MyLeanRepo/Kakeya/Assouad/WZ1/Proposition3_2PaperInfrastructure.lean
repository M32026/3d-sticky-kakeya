import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import MyLeanRepo.Kakeya.Assouad.TranslationInfrastructure
import MyLeanRepo.Kakeya.Streamlined.VolumeHelpers

/-!
# Closed infrastructure for the paper model of WZ1 Proposition 3.2
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

def wz1PaperGridCubeTranslation
    (scale : ℝ) (cell : ℤ × ℤ × ℤ) : Point3 :=
  WithLp.toLp 2
    ![((cell.1 : ℝ) * scale),
      ((cell.2.1 : ℝ) * scale),
      ((cell.2.2 : ℝ) * scale)]

private lemma floor_sub_paper_cell
    {scale value : ℝ} (hscale : scale ≠ 0) (cell : ℤ)
    (hfloor : ⌊value / scale⌋ = cell) :
    ⌊(value - (cell : ℝ) * scale) / scale⌋ = 0 := by
  have hquot :
      (value - (cell : ℝ) * scale) / scale =
        value / scale - (cell : ℝ) := by
    field_simp [hscale]
  rw [hquot, Int.floor_sub_intCast, hfloor]
  simp

private lemma floor_add_paper_cell
    {scale value : ℝ} (hscale : scale ≠ 0) (cell : ℤ)
    (hfloor : ⌊value / scale⌋ = 0) :
    ⌊(value + (cell : ℝ) * scale) / scale⌋ = cell := by
  have hquot :
      (value + (cell : ℝ) * scale) / scale =
        value / scale + (cell : ℝ) := by
    field_simp [hscale]
  rw [hquot, Int.floor_add_intCast, hfloor]
  simp

theorem wz1PaperGridCube_eq_translate
    {scale : ℝ} (hscale : 0 < scale)
    (cell : ℤ × ℤ × ℤ) :
    wz1PaperGridCube scale cell =
      (fun point : Point3 =>
          point + wz1PaperGridCubeTranslation scale cell) ''
        wz1PaperGridCube scale (0, 0, 0) := by
  ext point
  constructor
  · intro hpoint
    let shifted :=
      point - wz1PaperGridCubeTranslation scale cell
    refine ⟨shifted, ?_, by simp [shifted]⟩
    apply
      (mem_wz1PaperGridCube scale (0, 0, 0) shifted).mpr
    have hindex :=
      (mem_wz1PaperGridCube scale cell point).mp hpoint
    apply Prod.ext
    · simp only [wz1PaperGridIndex, gridIndex,
        shifted, wz1PaperGridCubeTranslation, PiLp.sub_apply]
      apply floor_sub_paper_cell hscale.ne' cell.1
      simpa [wz1PaperGridIndex, gridIndex] using
        congrArg Prod.fst hindex
    · apply Prod.ext
      · simp only [wz1PaperGridIndex, gridIndex,
          shifted, wz1PaperGridCubeTranslation, PiLp.sub_apply]
        apply floor_sub_paper_cell hscale.ne' cell.2.1
        simpa [wz1PaperGridIndex, gridIndex] using
          congrArg (fun index => index.2.1) hindex
      · simp only [wz1PaperGridIndex, gridIndex,
          shifted, wz1PaperGridCubeTranslation, PiLp.sub_apply]
        apply floor_sub_paper_cell hscale.ne' cell.2.2
        simpa [wz1PaperGridIndex, gridIndex] using
          congrArg (fun index => index.2.2) hindex
  · rintro ⟨shifted, hshifted, rfl⟩
    apply (mem_wz1PaperGridCube scale cell _).mpr
    have hindex :=
      (mem_wz1PaperGridCube scale (0, 0, 0) shifted).mp
        hshifted
    apply Prod.ext
    · simp only [wz1PaperGridIndex, gridIndex,
        wz1PaperGridCubeTranslation, PiLp.add_apply]
      apply floor_add_paper_cell hscale.ne' cell.1
      simpa [wz1PaperGridIndex, gridIndex] using
        congrArg Prod.fst hindex
    · apply Prod.ext
      · simp only [wz1PaperGridIndex, gridIndex,
          wz1PaperGridCubeTranslation, PiLp.add_apply]
        apply floor_add_paper_cell hscale.ne' cell.2.1
        simpa [wz1PaperGridIndex, gridIndex] using
          congrArg (fun index => index.2.1) hindex
      · simp only [wz1PaperGridIndex, gridIndex,
          wz1PaperGridCubeTranslation, PiLp.add_apply]
        apply floor_add_paper_cell hscale.ne' cell.2.2
        simpa [wz1PaperGridIndex, gridIndex] using
          congrArg (fun index => index.2.2) hindex

theorem wz1PaperGridCube_measurable
    {scale : ℝ} (cell : ℤ × ℤ × ℤ) :
    MeasurableSet (wz1PaperGridCube scale cell) := by
  have h0 :
      Measurable
        (fun point : Point3 =>
          ⌊point 0 / scale⌋) :=
    Measurable.floor (by fun_prop)
  have h1 :
      Measurable
        (fun point : Point3 =>
          ⌊point 1 / scale⌋) :=
    Measurable.floor (by fun_prop)
  have h2 :
      Measurable
        (fun point : Point3 =>
          ⌊point 2 / scale⌋) :=
    Measurable.floor (by fun_prop)
  have hindex :
      wz1PaperGridIndex scale =
        fun point =>
          (⌊point 0 / scale⌋,
            ⌊point 1 / scale⌋,
              ⌊point 2 / scale⌋) := by
    funext point
    rfl
  rw [wz1PaperGridCube]
  change
    MeasurableSet
      {point : Point3 |
        (⌊point 0 / scale⌋,
          ⌊point 1 / scale⌋,
            ⌊point 2 / scale⌋) = cell}
  exact
    (h0.prod (h1.prod h2))
      (MeasurableSet.singleton cell)

theorem wz1PaperGridCube_volume_eq
    {scale : ℝ} (hscale : 0 < scale)
    (first second : ℤ × ℤ × ℤ) :
    volume (wz1PaperGridCube scale first) =
      volume (wz1PaperGridCube scale second) := by
  rw [wz1PaperGridCube_eq_translate hscale first,
    wz1PaperGridCube_eq_translate hscale second]
  rw [TranslationInfrastructure.volume_translate
    (wz1PaperGridCube_measurable (0, 0, 0))]
  rw [TranslationInfrastructure.volume_translate
    (wz1PaperGridCube_measurable (0, 0, 0))]

theorem wz1PaperGridCube_volume_pos
    {scale : ℝ} (hscale : 0 < scale)
    (cell : ℤ × ℤ × ℤ) :
    0 < volume (wz1PaperGridCube scale cell) := by
  rw [wz1PaperGridCube_volume_eq hscale cell (0, 0, 0)]
  let center : Point3 :=
    WithLp.toLp 2 ![scale / 2, scale / 2, scale / 2]
  have hball :
      Metric.ball center (scale / 2) ⊆
        wz1PaperGridCube scale (0, 0, 0) := by
    intro point hpoint
    apply (mem_wz1PaperGridCube _ _ _).mpr
    apply Prod.ext
    · change ⌊point 0 / scale⌋ = 0
      apply Int.floor_eq_zero_iff.mpr
      have hcoord :
          |point 0 - scale / 2| < scale / 2 := by
        exact
          (PiLp.dist_apply_le point center 0).trans_lt
            hpoint
      constructor <;> dsimp only [center] at hcoord ⊢
      · have hnonneg : 0 ≤ point 0 := by
          rw [abs_lt] at hcoord
          linarith
        exact div_nonneg hnonneg hscale.le
      · rw [div_lt_one hscale]
        rw [abs_lt] at hcoord
        linarith
    · apply Prod.ext
      · change ⌊point 1 / scale⌋ = 0
        apply Int.floor_eq_zero_iff.mpr
        have hcoord :
            |point 1 - scale / 2| < scale / 2 := by
          exact
            (PiLp.dist_apply_le point center 1).trans_lt
              hpoint
        constructor <;> dsimp only [center] at hcoord ⊢
        · have hnonneg : 0 ≤ point 1 := by
            rw [abs_lt] at hcoord
            linarith
          exact div_nonneg hnonneg hscale.le
        · rw [div_lt_one hscale]
          rw [abs_lt] at hcoord
          linarith
      · change ⌊point 2 / scale⌋ = 0
        apply Int.floor_eq_zero_iff.mpr
        have hcoord :
            |point 2 - scale / 2| < scale / 2 := by
          exact
            (PiLp.dist_apply_le point center 2).trans_lt
              hpoint
        constructor <;> dsimp only [center] at hcoord ⊢
        · have hnonneg : 0 ≤ point 2 := by
            rw [abs_lt] at hcoord
            linarith
          exact div_nonneg hnonneg hscale.le
        · rw [div_lt_one hscale]
          rw [abs_lt] at hcoord
          linarith
  exact
    (Metric.measure_ball_pos volume center (by positivity)).trans_le
      (measure_mono hball)

theorem wz1PaperCubicalSaturation_eq_iUnion
    (scale : ℝ) (source : Set Point3) :
    wz1PaperCubicalSaturation scale source =
      ⋃ cell :
          {cell : ℤ × ℤ × ℤ //
            (source ∩ wz1PaperGridCube scale cell).Nonempty},
        wz1PaperGridCube scale cell.1 := by
  ext point
  constructor
  · rintro ⟨sourcePoint, hsourcePoint, hindex⟩
    let cell := wz1PaperGridIndex scale point
    apply Set.mem_iUnion.mpr
    refine
      ⟨⟨cell, sourcePoint, hsourcePoint,
          (mem_wz1PaperGridCube _ _ _).mpr hindex.symm⟩, ?_⟩
    exact (mem_wz1PaperGridCube _ _ _).mpr rfl
  · intro hpoint
    rcases Set.mem_iUnion.mp hpoint with
      ⟨cell, hpointCell⟩
    rcases cell.2 with
      ⟨sourcePoint, hsourcePoint, hsourceCell⟩
    exact
      ⟨sourcePoint, hsourcePoint,
        ((mem_wz1PaperGridCube _ _ _).mp
            hpointCell).trans
          ((mem_wz1PaperGridCube _ _ _).mp
            hsourceCell).symm⟩

theorem wz1PaperCubicalSaturation_measurable
    (scale : ℝ) (source : Set Point3) :
    MeasurableSet
      (wz1PaperCubicalSaturation scale source) := by
  rw [wz1PaperCubicalSaturation_eq_iUnion]
  apply MeasurableSet.iUnion
  intro cell
  exact wz1PaperGridCube_measurable cell.1

theorem wz1PaperCubicalSaturation_isCubical
    (scale : ℝ) (source : Set Point3) :
    ∀ point ∈ wz1PaperCubicalSaturation scale source,
      wz1PaperGridCube scale
          (wz1PaperGridIndex scale point) ⊆
        wz1PaperCubicalSaturation scale source := by
  rintro point ⟨sourcePoint, hsourcePoint, hpoint⟩
    other hother
  exact
    ⟨sourcePoint, hsourcePoint,
      ((mem_wz1PaperGridCube _ _ _).mp hother).trans
        hpoint⟩

theorem wz1PaperTubeCarrier_measurable
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    MeasurableSet (wz1PaperTubeCarrier tube) := by
  exact
    Metric.isClosed_cthickening.measurableSet.inter
      (Kakeya.Streamlined.measurableSet_axisBox 2 2 2)

theorem WZ1PaperTubeShading.union_measurable
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) :
    MeasurableSet shading.union := by
  have heq :
      shading.union =
        ⋃ index : Fin family.card,
          shading.carrier index := by
    ext point
    constructor
    · rintro ⟨index, hpoint⟩
      exact Set.mem_iUnion.mpr ⟨index, hpoint⟩
    · intro hpoint
      rcases Set.mem_iUnion.mp hpoint with
        ⟨index, hindex⟩
      exact ⟨index, hindex⟩
  rw [heq]
  exact
    MeasurableSet.iUnion fun index =>
      shading.measurable_carrier index

/-- A finite integer box containing all paper cells meeting `[-1,1]^3`. -/
def wz1PaperGridIndicesInWindow
    (scale : ℝ) (hscale : 0 < scale) :
    Finset (ℤ × ℤ × ℤ) :=
  let bound : ℤ := ⌈1 / scale⌉ + 1
  (Finset.Icc (-bound) bound).product
    ((Finset.Icc (-bound) bound).product
      (Finset.Icc (-bound) bound))

/-- Finite literal paper cells meeting a shading in the cropped box. -/
def wz1PaperActiveCells
    {scale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily scale}
    (shading : WZ1PaperTubeShading family)
    (hscale : 0 < scale) :
    Finset (ℤ × ℤ × ℤ) :=
  (wz1PaperGridIndicesInWindow scale hscale).filter
    fun cell =>
      (shading.union ∩ wz1PaperGridCube scale cell).Nonempty

@[simp] theorem mem_wz1PaperActiveCells
    {scale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily scale}
    (shading : WZ1PaperTubeShading family)
    (hscale : 0 < scale)
    (cell : ℤ × ℤ × ℤ) :
    cell ∈ wz1PaperActiveCells shading hscale ↔
      cell ∈ wz1PaperGridIndicesInWindow scale hscale ∧
        (shading.union ∩
          wz1PaperGridCube scale cell).Nonempty := by
  simp [wz1PaperActiveCells]

theorem WZ1PaperIsCubicalShading.inter_activeCell_eq
    {scale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily scale}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hscale : 0 < scale)
    {cell : ℤ × ℤ × ℤ}
    (hcell : cell ∈ wz1PaperActiveCells shading hscale) :
    shading.union ∩ wz1PaperGridCube scale cell =
      wz1PaperGridCube scale cell := by
  apply Set.inter_eq_right.mpr
  intro point hpointCell
  rcases
      ((mem_wz1PaperActiveCells shading hscale cell).mp
        hcell).2 with
    ⟨sourcePoint, hsourceUnion, hsourceCell⟩
  rcases hsourceUnion with ⟨index, hsourceCarrier⟩
  refine ⟨index, ?_⟩
  apply hcubical index sourcePoint hsourceCarrier
  have hsourceIndex :
      wz1PaperGridIndex scale sourcePoint = cell :=
    (mem_wz1PaperGridCube scale cell sourcePoint).mp
      hsourceCell
  have hpointIndex :
      wz1PaperGridIndex scale point = cell :=
    (mem_wz1PaperGridCube scale cell point).mp
      hpointCell
  apply
    (mem_wz1PaperGridCube scale
      (wz1PaperGridIndex scale sourcePoint) point).mpr
  exact hpointIndex.trans hsourceIndex.symm

theorem WZ1PaperIsCubicalShading.activeCell_volume_eq
    {scale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily scale}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hscale : 0 < scale)
    {first second : ℤ × ℤ × ℤ}
    (hfirst : first ∈ wz1PaperActiveCells shading hscale)
    (hsecond : second ∈ wz1PaperActiveCells shading hscale) :
    volume
        (shading.union ∩ wz1PaperGridCube scale first) =
      volume
        (shading.union ∩ wz1PaperGridCube scale second) := by
  rw [hcubical.inter_activeCell_eq hscale hfirst,
    hcubical.inter_activeCell_eq hscale hsecond]
  exact wz1PaperGridCube_volume_eq hscale first second

end Kakeya.Assouad
