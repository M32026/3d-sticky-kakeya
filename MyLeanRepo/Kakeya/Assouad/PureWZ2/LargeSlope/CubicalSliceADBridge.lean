import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperADFiniteUnion
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ADTransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicADTransfer
import MyLeanRepo.Kakeya.Assouad.PropStickyGridCubeBoxHelpers

/-!
# From exact-slice AD to narrow-slab AD on cubical shadings

A point of a cubical paper shading may be moved vertically to the lower face
of its grid cell without leaving the same tube shading.  If the slope is
one-Lipschitz, its height-dependent scalar projection changes by at most one
grid scale.  Consequently a slab meeting only finitely many height cells is
controlled by the finite union of the corresponding exact-slice AD sets.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- Replace only the height coordinate of a point. -/
def pureWZ2ReplaceHeight (point : Point3) (height : ℝ) : Point3 :=
  point3 (point 0) (point 1) height

/-- The lower-face height of the paper grid cell containing a point. -/
def pureWZ2PaperCellLowerHeight (delta : ℝ) (point : Point3) : ℝ :=
  (Int.floor (point 2 / delta) : ℝ) * delta

@[simp] theorem pureWZ2ReplaceHeight_apply_zero
    (point : Point3) (height : ℝ) :
    pureWZ2ReplaceHeight point height 0 = point 0 := by
  simp [pureWZ2ReplaceHeight, point3]

@[simp] theorem pureWZ2ReplaceHeight_apply_one
    (point : Point3) (height : ℝ) :
    pureWZ2ReplaceHeight point height 1 = point 1 := by
  simp [pureWZ2ReplaceHeight, point3]

@[simp] theorem pureWZ2ReplaceHeight_apply_two
    (point : Point3) (height : ℝ) :
    pureWZ2ReplaceHeight point height 2 = height := by
  simp [pureWZ2ReplaceHeight, point3]

/-- Moving a point to the lower face of its height cell preserves its complete
three-dimensional paper grid index. -/
theorem pureWZ2ReplaceHeight_lower_gridIndex
    {delta : ℝ} (hdelta : 0 < delta) (point : Point3) :
    wz1PaperGridIndex delta
        (pureWZ2ReplaceHeight point
          (pureWZ2PaperCellLowerHeight delta point)) =
      wz1PaperGridIndex delta point := by
  unfold wz1PaperGridIndex gridIndex
  apply Prod.ext
  · simpa only using congrArg Int.floor <|
      congrArg (fun value : ℝ => value / delta)
        (pureWZ2ReplaceHeight_apply_zero point _)
  · apply Prod.ext
    · simpa only using congrArg Int.floor <|
        congrArg (fun value : ℝ => value / delta)
          (pureWZ2ReplaceHeight_apply_one point _)
    · simp only [pureWZ2ReplaceHeight_apply_two,
        pureWZ2PaperCellLowerHeight]
      have hcancel :
          ((Int.floor (point 2 / delta) : ℝ) * delta) / delta =
            (Int.floor (point 2 / delta) : ℝ) := by
        field_simp [hdelta.ne']
      rw [hcancel, Int.floor_intCast]

/-- A point and the lower face of its height cell differ in height by less
than one grid scale. -/
theorem pureWZ2PaperCellLowerHeight_close
    {delta : ℝ} (hdelta : 0 < delta) (point : Point3) :
    |point 2 - pureWZ2PaperCellLowerHeight delta point| ≤ delta := by
  let quotient := point 2 / delta
  have hlower : (Int.floor quotient : ℝ) ≤ quotient := Int.floor_le quotient
  have hupper : quotient < (Int.floor quotient : ℝ) + 1 :=
    Int.lt_floor_add_one quotient
  have hpoint : point 2 = quotient * delta := by
    dsimp only [quotient]
    field_simp [hdelta.ne']
  have hnonnegative :
      0 ≤ point 2 - pureWZ2PaperCellLowerHeight delta point := by
    rw [hpoint]
    unfold pureWZ2PaperCellLowerHeight
    exact sub_nonneg.mpr <| by
      nlinarith [mul_le_mul_of_nonneg_right hlower hdelta.le]
  rw [abs_of_nonneg hnonnegative, hpoint]
  unfold pureWZ2PaperCellLowerHeight
  have hstrict :
      quotient * delta - (Int.floor quotient : ℝ) * delta < delta := by
    nlinarith [mul_lt_mul_of_pos_right hupper hdelta]
  exact hstrict.le

/-- Cubicality lets us replace the height by the lower face of the occupied
grid cell without leaving the same indexed shading carrier. -/
theorem WZ1PaperIsCubicalShading.replaceHeight_lower_mem
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hdelta : 0 < delta) {index : Fin family.card}
    {point : Point3} (hpoint : point ∈ shading.carrier index) :
    pureWZ2ReplaceHeight point
        (pureWZ2PaperCellLowerHeight delta point) ∈
      shading.carrier index := by
  apply hcubical index point hpoint
  apply (mem_wz1PaperGridCube _ _ _).mpr
  exact pureWZ2ReplaceHeight_lower_gridIndex hdelta point

/-- The height-dependent global-grain projection of a cubical point is within
one grid scale of the exact-slice projection at its cell's lower face. -/
theorem WZ1PaperIsCubicalShading.exists_lower_slice_projection
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hdelta : 0 < delta) (slope : ℝ → ℝ)
    (hslope : ∀ first ∈ Set.Icc (-1 : ℝ) 1,
      ∀ second ∈ Set.Icc (-1 : ℝ) 1,
        |slope first - slope second| ≤ |first - second|)
    {point : Point3} (hpoint : point ∈ shading.union) :
    let cellHeight := pureWZ2PaperCellLowerHeight delta point
    ∃ source ∈ horizontalSlice shading.union cellHeight,
      dist
          (inner ℝ point (globalGrainDirection (slope (point 2))))
          (inner ℝ source (globalGrainDirection (slope cellHeight))) ≤
        delta := by
  rcases hpoint with ⟨index, hpoint⟩
  let cellHeight := pureWZ2PaperCellLowerHeight delta point
  let source := pureWZ2ReplaceHeight point cellHeight
  have hsourceCarrier : source ∈ shading.carrier index := by
    exact hcubical.replaceHeight_lower_mem hdelta hpoint
  have hsourceUnion : source ∈ shading.union := ⟨index, hsourceCarrier⟩
  have hpointBox := (shading.subset_body index hpoint).2
  have hsourceBox := (shading.subset_body index hsourceCarrier).2
  have hpointHeight : point 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    exact abs_le.mp <| by
      simpa [Kakeya.Streamlined.axisBox] using hpointBox.2.2
  have hsourceHeight : cellHeight ∈ Set.Icc (-1 : ℝ) 1 := by
    exact abs_le.mp <| by
      simpa [source, Kakeya.Streamlined.axisBox] using hsourceBox.2.2
  have hslopeClose := hslope (point 2) hpointHeight cellHeight hsourceHeight
  have hheightClose := pureWZ2PaperCellLowerHeight_close hdelta point
  have hpointOne : |point 1| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hpointBox.2.1
  refine ⟨source, ⟨hsourceUnion, by
    exact pureWZ2ReplaceHeight_apply_two point cellHeight⟩, ?_⟩
  rw [Real.dist_eq]
  have hprojection :
      inner ℝ point (globalGrainDirection (slope (point 2))) -
          inner ℝ source (globalGrainDirection (slope cellHeight)) =
        (slope (point 2) - slope cellHeight) * point 1 := by
    simp [source, pureWZ2ReplaceHeight, globalGrainDirection,
      PiLp.inner_apply, Fin.sum_univ_succ, point3]
    ring
  rw [hprojection, abs_mul]
  calc
    |slope (point 2) - slope cellHeight| * |point 1|
        ≤ |point 2 - cellHeight| * 1 := by gcongr
    _ ≤ delta := by simpa using hheightClose

/-- AD bridge for a cubical height-dependent projection on a region whose
occupied height cells belong to a supplied finite set. -/
theorem WZ1PaperIsCubicalShading.globalProjection_restrict_heightCells_ad
    {delta alpha : ℝ} {C : ENNReal}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hdelta : 0 < delta) (slope : ℝ → ℝ)
    (hslope : ∀ first ∈ Set.Icc (-1 : ℝ) 1,
      ∀ second ∈ Set.Icc (-1 : ℝ) 1,
        |slope first - slope second| ≤ |first - second|)
    (heightCells : Finset ℤ) (hheightCells : heightCells.Nonempty)
    (region : Set Point3)
    (hregion : region ⊆ shading.union)
    (hcell : ∀ point ∈ region,
      Int.floor (point 2 / delta) ∈ heightCells)
    (hexactAD : ∀ cell ∈ heightCells,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection
          (slope ((cell : ℝ) * delta)))
          (horizontalSlice shading.union ((cell : ℝ) * delta)))
        delta alpha C) :
    PureWZ2PaperADSet1 (globalGrainProjection slope region)
      delta alpha (6 * ((heightCells.card : ENNReal) * C)) := by
  let pieces : ℤ → Set ℝ := fun cell =>
    scalarProjection (globalGrainDirection (slope ((cell : ℝ) * delta)))
      (horizontalSlice shading.union ((cell : ℝ) * delta))
  apply PureWZ2PaperADSet1.of_finite_nearby_witness
    hheightCells (fun cell hcell => hexactAD cell hcell)
      (D := delta) (pieces := pieces)
  · rintro value ⟨point, hpoint, rfl⟩
    have hpointUnion := hregion hpoint
    rcases hcubical.exists_lower_slice_projection hdelta slope hslope
        hpointUnion with ⟨source, hsource, hdist⟩
    let cell : ℤ := Int.floor (point 2 / delta)
    have hcellMem : cell ∈ heightCells := hcell point hpoint
    refine ⟨cell, hcellMem,
      inner ℝ source (globalGrainDirection (slope ((cell : ℝ) * delta))),
      ?_, ?_⟩
    · exact ⟨source, by simpa [pieces, cell,
        pureWZ2PaperCellLowerHeight] using hsource, rfl⟩
    · simpa [cell, pureWZ2PaperCellLowerHeight] using hdist
  · exact hdelta.le
  · exact le_rfl

/-- Abstract target-projection bridge used by the final affine rescaling.
Each target scalar is compared with the affine image of the source projection
at the lower face of the source point's cubical height cell. -/
theorem WZ1PaperIsCubicalShading.targetProjection_ad_of_source_witness
    {sourceDelta targetDelta alpha a b D : ℝ} {C : ENNReal}
    {family : Kakeya.Streamlined.TubeFamily sourceDelta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (slope : ℝ → ℝ)
    (heightCells : Finset ℤ) (hheightCells : heightCells.Nonempty)
    (hcellHeight : ∀ cell ∈ heightCells,
      (cell : ℝ) * sourceDelta ∈ Set.Icc (-1 : ℝ) 1)
    (hsourceAD : ∀ height ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (slope height))
          (horizontalSlice shading.union height))
        sourceDelta alpha C)
    (ha : 0 < a) (hbase : a * sourceDelta ≤ targetDelta)
    (target : Set ℝ)
    (hwitness : ∀ value ∈ target,
      ∃ point ∈ shading.union,
        Int.floor (point 2 / sourceDelta) ∈ heightCells ∧
        dist value
          (a * inner ℝ
              (pureWZ2ReplaceHeight point
                (pureWZ2PaperCellLowerHeight sourceDelta point))
              (globalGrainDirection
                (slope (pureWZ2PaperCellLowerHeight sourceDelta point))) + b) ≤ D)
    (hDNonnegative : 0 ≤ D) (hDTarget : D ≤ targetDelta) :
    PureWZ2PaperADSet1 target targetDelta alpha
      (6 * ((heightCells.card : ENNReal) * C)) := by
  let pieces : ℤ → Set ℝ := fun cell =>
    (fun value : ℝ => a * value + b) ''
      scalarProjection (globalGrainDirection (slope ((cell : ℝ) * sourceDelta)))
        (horizontalSlice shading.union ((cell : ℝ) * sourceDelta))
  have hpieces : ∀ cell ∈ heightCells,
      PureWZ2PaperADSet1 (pieces cell) targetDelta alpha C := by
    intro cell hcell
    have haffine := PureWZ2PaperADSet1.affine_transfer
      (b := b) (hsourceAD ((cell : ℝ) * sourceDelta)
        (hcellHeight cell hcell)) ha
    exact PureWZ2PaperADSet1.weaken_scale haffine htargetDelta hbase
  apply PureWZ2PaperADSet1.of_finite_nearby_witness
    hheightCells hpieces (D := D) (target := target)
  · intro value hvalue
    rcases hwitness value hvalue with
      ⟨point, hpoint, hcell, hdist⟩
    let cell : ℤ := Int.floor (point 2 / sourceDelta)
    let source := pureWZ2ReplaceHeight point
      (pureWZ2PaperCellLowerHeight sourceDelta point)
    have hsourceCarrier : source ∈ shading.union := by
      rcases hpoint with ⟨index, hpointIndex⟩
      exact ⟨index, hcubical.replaceHeight_lower_mem
        hsourceDelta hpointIndex⟩
    have hsourceSlice : source ∈ horizontalSlice shading.union
        ((cell : ℝ) * sourceDelta) := by
      refine ⟨hsourceCarrier, ?_⟩
      simp [source, cell, pureWZ2PaperCellLowerHeight]
    refine ⟨cell, hcell,
      a * inner ℝ source
          (globalGrainDirection (slope ((cell : ℝ) * sourceDelta))) + b,
      ?_, ?_⟩
    · exact ⟨inner ℝ source
          (globalGrainDirection (slope ((cell : ℝ) * sourceDelta))),
        ⟨source, hsourceSlice, rfl⟩, rfl⟩
    · simpa [source, cell, pureWZ2PaperCellLowerHeight] using hdist
  · exact hDNonnegative
  · exact hDTarget

/-- General-radius version of `targetProjection_ad_of_source_witness`.  This
is the form needed after the final cubical saturation in the coupled route:
the steep public slope can enlarge one target grid cell by a finite factor,
so that factor is kept explicitly instead of being incorrectly absorbed into
one target scale. -/
theorem WZ1PaperIsCubicalShading.targetProjection_ad_of_source_witness_general
    {sourceDelta targetDelta alpha a b D : ℝ} {C : ENNReal}
    {family : Kakeya.Streamlined.TubeFamily sourceDelta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (slope : ℝ → ℝ)
    (heightCells : Finset ℤ) (hheightCells : heightCells.Nonempty)
    (hcellHeight : ∀ cell ∈ heightCells,
      (cell : ℝ) * sourceDelta ∈ Set.Icc (-1 : ℝ) 1)
    (hsourceAD : ∀ height ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (slope height))
          (horizontalSlice shading.union height))
        sourceDelta alpha C)
    (ha : 0 < a) (hbase : a * sourceDelta ≤ targetDelta)
    (target : Set ℝ)
    (hwitness : ∀ value ∈ target,
      ∃ point ∈ shading.union,
        Int.floor (point 2 / sourceDelta) ∈ heightCells ∧
        dist value
          (a * inner ℝ
              (pureWZ2ReplaceHeight point
                (pureWZ2PaperCellLowerHeight sourceDelta point))
              (globalGrainDirection
                (slope (pureWZ2PaperCellLowerHeight sourceDelta point))) + b) ≤ D)
    (hD : 0 < D) :
    PureWZ2PaperADSet1 target targetDelta alpha
      ((2 * (Nat.ceil (D / targetDelta) + 1) : ENNReal) ^ 3 *
        ((heightCells.card : ENNReal) * C)) := by
  let pieces : ℤ → Set ℝ := fun cell =>
    (fun value : ℝ => a * value + b) ''
      scalarProjection (globalGrainDirection (slope ((cell : ℝ) * sourceDelta)))
        (horizontalSlice shading.union ((cell : ℝ) * sourceDelta))
  have hpieces : ∀ cell ∈ heightCells,
      PureWZ2PaperADSet1 (pieces cell) targetDelta alpha C := by
    intro cell hcell
    have haffine := PureWZ2PaperADSet1.affine_transfer
      (b := b) (hsourceAD ((cell : ℝ) * sourceDelta)
        (hcellHeight cell hcell)) ha
    exact PureWZ2PaperADSet1.weaken_scale haffine htargetDelta hbase
  have hunion : PureWZ2PaperADSet1
      (⋃ cell ∈ heightCells, pieces cell) targetDelta alpha
        ((heightCells.card : ENNReal) * C) :=
    PureWZ2PaperADSet1.finite_iUnion hheightCells hpieces
  apply hunion.of_subset_cthickening_general (epsilon := D)
  · intro value hvalue
    rcases hwitness value hvalue with
      ⟨point, hpoint, hcell, hdist⟩
    let cell : ℤ := Int.floor (point 2 / sourceDelta)
    let source := pureWZ2ReplaceHeight point
      (pureWZ2PaperCellLowerHeight sourceDelta point)
    have hsourceCarrier : source ∈ shading.union := by
      rcases hpoint with ⟨index, hpointIndex⟩
      exact ⟨index, hcubical.replaceHeight_lower_mem
        hsourceDelta hpointIndex⟩
    have hsourceSlice : source ∈ horizontalSlice shading.union
        ((cell : ℝ) * sourceDelta) := by
      refine ⟨hsourceCarrier, ?_⟩
      simp [source, cell, pureWZ2PaperCellLowerHeight]
    refine ⟨a * inner ℝ source
        (globalGrainDirection (slope ((cell : ℝ) * sourceDelta))) + b,
      ?_, ?_⟩
    · exact Set.mem_iUnion.mpr ⟨cell, Set.mem_iUnion.mpr ⟨hcell,
        ⟨inner ℝ source
            (globalGrainDirection (slope ((cell : ℝ) * sourceDelta))),
          ⟨source, hsourceSlice, rfl⟩, rfl⟩⟩⟩
    · simpa [source, cell, pureWZ2PaperCellLowerHeight] using hdist
  · exact hD

/-- General-radius finite-slice transfer with one affine translation for each
source height cell.  The linear scale must be common, but translations may
depend on the slice; finite-union AD is insensitive to those translations. -/
theorem WZ1PaperIsCubicalShading.targetProjection_ad_of_source_witness_indexed
    {sourceDelta targetDelta alpha a D : ℝ} {C : ENNReal}
    {family : Kakeya.Streamlined.TubeFamily sourceDelta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (slope : ℝ → ℝ)
    (heightCells : Finset ℤ) (hheightCells : heightCells.Nonempty)
    (hcellHeight : ∀ cell ∈ heightCells,
      (cell : ℝ) * sourceDelta ∈ Set.Icc (-1 : ℝ) 1)
    (hsourceAD : ∀ height ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (slope height))
          (horizontalSlice shading.union height))
        sourceDelta alpha C)
    (ha : 0 < a) (hbase : a * sourceDelta ≤ targetDelta)
    (offset : ℤ → ℝ) (target : Set ℝ)
    (hwitness : ∀ value ∈ target,
      ∃ point ∈ shading.union,
        let cell := Int.floor (point 2 / sourceDelta)
        cell ∈ heightCells ∧
          dist value
            (a * inner ℝ
                (pureWZ2ReplaceHeight point
                  (pureWZ2PaperCellLowerHeight sourceDelta point))
                (globalGrainDirection
                  (slope (pureWZ2PaperCellLowerHeight sourceDelta point))) +
              offset cell) ≤ D)
    (hD : 0 < D) :
    PureWZ2PaperADSet1 target targetDelta alpha
      ((2 * (Nat.ceil (D / targetDelta) + 1) : ENNReal) ^ 3 *
        ((heightCells.card : ENNReal) * C)) := by
  let pieces : ℤ → Set ℝ := fun cell =>
    (fun value : ℝ => a * value + offset cell) ''
      scalarProjection (globalGrainDirection (slope ((cell : ℝ) * sourceDelta)))
        (horizontalSlice shading.union ((cell : ℝ) * sourceDelta))
  have hpieces : ∀ cell ∈ heightCells,
      PureWZ2PaperADSet1 (pieces cell) targetDelta alpha C := by
    intro cell hcell
    have haffine := PureWZ2PaperADSet1.affine_transfer
      (b := offset cell) (hsourceAD ((cell : ℝ) * sourceDelta)
        (hcellHeight cell hcell)) ha
    exact PureWZ2PaperADSet1.weaken_scale haffine htargetDelta hbase
  have hunion : PureWZ2PaperADSet1
      (⋃ cell ∈ heightCells, pieces cell) targetDelta alpha
        ((heightCells.card : ENNReal) * C) :=
    PureWZ2PaperADSet1.finite_iUnion hheightCells hpieces
  apply hunion.of_subset_cthickening_general (epsilon := D)
  · intro value hvalue
    rcases hwitness value hvalue with
      ⟨point, hpoint, hcell, hdist⟩
    let cell : ℤ := Int.floor (point 2 / sourceDelta)
    let source := pureWZ2ReplaceHeight point
      (pureWZ2PaperCellLowerHeight sourceDelta point)
    have hsourceCarrier : source ∈ shading.union := by
      rcases hpoint with ⟨index, hpointIndex⟩
      exact ⟨index, hcubical.replaceHeight_lower_mem
        hsourceDelta hpointIndex⟩
    have hsourceSlice : source ∈ horizontalSlice shading.union
        ((cell : ℝ) * sourceDelta) := by
      refine ⟨hsourceCarrier, ?_⟩
      simp [source, cell, pureWZ2PaperCellLowerHeight]
    refine ⟨a * inner ℝ source
        (globalGrainDirection (slope ((cell : ℝ) * sourceDelta))) +
          offset cell, ?_, ?_⟩
    · exact Set.mem_iUnion.mpr ⟨cell, Set.mem_iUnion.mpr ⟨hcell,
        ⟨inner ℝ source
            (globalGrainDirection (slope ((cell : ℝ) * sourceDelta))),
          ⟨source, hsourceSlice, rfl⟩, rfl⟩⟩⟩
    · simpa [source, cell, pureWZ2PaperCellLowerHeight] using hdist
  · exact hD

/-- All-height variant of the indexed finite-slice transfer.  It is useful
when the source shading is supported in the paper height window but the fixed
finite cell window deliberately extends past its endpoints: the caller proves
the out-of-window exact slices empty once, and no artificial clipping of the
cell set is needed here. -/
theorem WZ1PaperIsCubicalShading.targetProjection_ad_of_source_witness_indexed_all
    {sourceDelta targetDelta alpha a D : ℝ} {C : ENNReal}
    {family : Kakeya.Streamlined.TubeFamily sourceDelta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (slope : ℝ → ℝ)
    (heightCells : Finset ℤ) (hheightCells : heightCells.Nonempty)
    (hsourceAD : ∀ height : ℝ,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (slope height))
          (horizontalSlice shading.union height))
        sourceDelta alpha C)
    (ha : 0 < a) (hbase : a * sourceDelta ≤ targetDelta)
    (offset : ℤ → ℝ) (target : Set ℝ)
    (hwitness : ∀ value ∈ target,
      ∃ point ∈ shading.union,
        let cell := Int.floor (point 2 / sourceDelta)
        cell ∈ heightCells ∧
          dist value
            (a * inner ℝ
                (pureWZ2ReplaceHeight point
                  (pureWZ2PaperCellLowerHeight sourceDelta point))
                (globalGrainDirection
                  (slope (pureWZ2PaperCellLowerHeight sourceDelta point))) +
              offset cell) ≤ D)
    (hD : 0 < D) :
    PureWZ2PaperADSet1 target targetDelta alpha
      ((2 * (Nat.ceil (D / targetDelta) + 1) : ENNReal) ^ 3 *
        ((heightCells.card : ENNReal) * C)) := by
  let pieces : ℤ → Set ℝ := fun cell =>
    (fun value : ℝ => a * value + offset cell) ''
      scalarProjection (globalGrainDirection (slope ((cell : ℝ) * sourceDelta)))
        (horizontalSlice shading.union ((cell : ℝ) * sourceDelta))
  have hpieces : ∀ cell ∈ heightCells,
      PureWZ2PaperADSet1 (pieces cell) targetDelta alpha C := by
    intro cell _hcell
    have haffine := PureWZ2PaperADSet1.affine_transfer
      (b := offset cell) (hsourceAD ((cell : ℝ) * sourceDelta)) ha
    exact PureWZ2PaperADSet1.weaken_scale haffine htargetDelta hbase
  have hunion : PureWZ2PaperADSet1
      (⋃ cell ∈ heightCells, pieces cell) targetDelta alpha
        ((heightCells.card : ENNReal) * C) :=
    PureWZ2PaperADSet1.finite_iUnion hheightCells hpieces
  apply hunion.of_subset_cthickening_general (epsilon := D)
  · intro value hvalue
    rcases hwitness value hvalue with
      ⟨point, hpoint, hcell, hdist⟩
    let cell : ℤ := Int.floor (point 2 / sourceDelta)
    let source := pureWZ2ReplaceHeight point
      (pureWZ2PaperCellLowerHeight sourceDelta point)
    have hsourceCarrier : source ∈ shading.union := by
      rcases hpoint with ⟨index, hpointIndex⟩
      exact ⟨index, hcubical.replaceHeight_lower_mem
        hsourceDelta hpointIndex⟩
    have hsourceSlice : source ∈ horizontalSlice shading.union
        ((cell : ℝ) * sourceDelta) := by
      refine ⟨hsourceCarrier, ?_⟩
      simp [source, cell, pureWZ2PaperCellLowerHeight]
    refine ⟨a * inner ℝ source
        (globalGrainDirection (slope ((cell : ℝ) * sourceDelta))) +
          offset cell, ?_, ?_⟩
    · exact Set.mem_iUnion.mpr ⟨cell, Set.mem_iUnion.mpr ⟨hcell,
        ⟨inner ℝ source
            (globalGrainDirection (slope ((cell : ℝ) * sourceDelta))),
          ⟨source, hsourceSlice, rfl⟩, rfl⟩⟩⟩
    · simpa [source, cell, pureWZ2PaperCellLowerHeight] using hdist
  · exact hD

/-- Variable-coefficient version of the all-height finite-slice transfer.
Each source height may use its own positive affine coefficient.  The proof is
the same finite-union argument; only the scale weakening is uniformized by
the pointwise bound `coefficient cell * sourceDelta ≤ targetDelta`. -/
theorem WZ1PaperIsCubicalShading.targetProjection_ad_of_source_witness_variable_all
    {sourceDelta targetDelta alpha D : ℝ} {C : ENNReal}
    {family : Kakeya.Streamlined.TubeFamily sourceDelta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (slope : ℝ → ℝ)
    (heightCells : Finset ℤ) (hheightCells : heightCells.Nonempty)
    (hsourceAD : ∀ height : ℝ,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (slope height))
          (horizontalSlice shading.union height))
        sourceDelta alpha C)
    (coefficient : ℤ → ℝ) (hcoefficient : ∀ cell, 0 < coefficient cell)
    (hbase : ∀ cell, coefficient cell * sourceDelta ≤ targetDelta)
    (offset : ℤ → ℝ) (target : Set ℝ)
    (hwitness : ∀ value ∈ target,
      ∃ point ∈ shading.union,
        let cell := Int.floor (point 2 / sourceDelta)
        cell ∈ heightCells ∧
          dist value
            (coefficient cell * inner ℝ
                (pureWZ2ReplaceHeight point
                  (pureWZ2PaperCellLowerHeight sourceDelta point))
                (globalGrainDirection
                  (slope (pureWZ2PaperCellLowerHeight sourceDelta point))) +
              offset cell) ≤ D)
    (hD : 0 < D) :
    PureWZ2PaperADSet1 target targetDelta alpha
      ((2 * (Nat.ceil (D / targetDelta) + 1) : ENNReal) ^ 3 *
        ((heightCells.card : ENNReal) * C)) := by
  let pieces : ℤ → Set ℝ := fun cell =>
    (fun value : ℝ => coefficient cell * value + offset cell) ''
      scalarProjection (globalGrainDirection (slope ((cell : ℝ) * sourceDelta)))
        (horizontalSlice shading.union ((cell : ℝ) * sourceDelta))
  have hpieces : ∀ cell ∈ heightCells,
      PureWZ2PaperADSet1 (pieces cell) targetDelta alpha C := by
    intro cell _hcell
    have haffine := PureWZ2PaperADSet1.affine_transfer
      (b := offset cell) (hsourceAD ((cell : ℝ) * sourceDelta))
      (hcoefficient cell)
    exact PureWZ2PaperADSet1.weaken_scale haffine htargetDelta (hbase cell)
  have hunion : PureWZ2PaperADSet1
      (⋃ cell ∈ heightCells, pieces cell) targetDelta alpha
        ((heightCells.card : ENNReal) * C) :=
    PureWZ2PaperADSet1.finite_iUnion hheightCells hpieces
  apply hunion.of_subset_cthickening_general (epsilon := D)
  · intro value hvalue
    rcases hwitness value hvalue with
      ⟨point, hpoint, hcell, hdist⟩
    let cell : ℤ := Int.floor (point 2 / sourceDelta)
    let source := pureWZ2ReplaceHeight point
      (pureWZ2PaperCellLowerHeight sourceDelta point)
    have hsourceCarrier : source ∈ shading.union := by
      rcases hpoint with ⟨index, hpointIndex⟩
      exact ⟨index, hcubical.replaceHeight_lower_mem
        hsourceDelta hpointIndex⟩
    have hsourceSlice : source ∈ horizontalSlice shading.union
        ((cell : ℝ) * sourceDelta) := by
      refine ⟨hsourceCarrier, ?_⟩
      simp [source, cell, pureWZ2PaperCellLowerHeight]
    refine ⟨coefficient cell * inner ℝ source
        (globalGrainDirection (slope ((cell : ℝ) * sourceDelta))) +
          offset cell, ?_, ?_⟩
    · exact Set.mem_iUnion.mpr ⟨cell, Set.mem_iUnion.mpr ⟨hcell,
        ⟨inner ℝ source
            (globalGrainDirection (slope ((cell : ℝ) * sourceDelta))),
          ⟨source, hsourceSlice, rfl⟩, rfl⟩⟩⟩
    · simpa [source, cell, pureWZ2PaperCellLowerHeight] using hdist
  · exact hD

end Kakeya.Assouad

end
