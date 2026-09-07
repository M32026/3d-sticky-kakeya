import MyLeanRepo.Kakeya.Assouad.PropStickyGridCubeBoxHelpers
import MyLeanRepo.Kakeya.AssertionD

/-!
# Local volume of an ordinary tube inside a grid cube

If a point of a side-`rho` paper grid cube lies within `5 * rho / 6` of the
axis segment of an ordinary `rho`-tube, then a fixed proportion of that grid
cube lies in the ordinary tube.  The proof inserts a closed axis-aligned box
of side `rho / 18`, choosing the inward direction separately in each
coordinate.  This also handles points on the closed faces of the half-open
grid cube.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

private theorem volume_closedBox_three
    (lo hi : Fin 3 → ℝ) (hlohi : ∀ i, lo i ≤ hi i) :
    volume ((WithLp.toLp 2) '' Set.Icc lo hi) =
      ENNReal.ofReal
        ((hi 0 - lo 0) * (hi 1 - lo 1) * (hi 2 - lo 2)) := by
  let toLp : (Fin 3 → ℝ) → Point3 := WithLp.toLp 2
  have hpreserving : MeasurePreserving toLp volume volume :=
    PiLp.volume_preserving_toLp (ι := Fin 3)
  have hinjective : Function.Injective toLp := by
    intro x y hxy
    simpa [toLp, WithLp.toLp_injective] using hxy
  have hcontinuous : Continuous toLp :=
    PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)
  have himage_measurable : MeasurableSet (toLp '' Set.Icc lo hi) := by
    have himage :
        toLp '' Set.Icc lo hi =
          (fun x : Point3 => x.ofLp) ⁻¹' Set.Icc lo hi := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa [WithLp.ofLp_toLp] using hx
      · intro hy
        exact ⟨y.ofLp, hy, by simp [toLp]⟩
    rw [himage]
    exact
      (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin 3 => ℝ)).measurable
        measurableSet_Icc
  have hvolume :
      volume (toLp '' Set.Icc lo hi) = volume (Set.Icc lo hi) := by
    calc
      volume (toLp '' Set.Icc lo hi) =
          Measure.map toLp volume (toLp '' Set.Icc lo hi) := by
            rw [hpreserving.map_eq]
      _ = volume (toLp ⁻¹' (toLp '' Set.Icc lo hi)) :=
        Measure.map_apply hcontinuous.measurable himage_measurable
      _ = volume (Set.Icc lo hi) := by
        rw [Set.preimage_image_eq _ hinjective]
  rw [hvolume, Real.volume_Icc_pi]
  simp [Fin.prod_univ_succ, ← ENNReal.ofReal_mul,
    sub_nonneg.mpr (hlohi 0), sub_nonneg.mpr (hlohi 1)]
  ; ring_nf

private lemma norm_le_three_mul_of_coordinate_abs_le
    {v : Point3} {s : ℝ} (_hs : 0 ≤ s)
    (hcoord : ∀ i : Fin 3, |v i| ≤ s) :
    ‖v‖ ≤ 3 * s := by
  have hv :
      v = ∑ i : Fin 3,
        (PiLp.single (2 : ENNReal) i (v i) : Point3) := by
    ext i
    simp
  calc
    ‖v‖ =
        ‖∑ i : Fin 3,
          (PiLp.single (2 : ENNReal) i (v i) : Point3)‖ :=
      congrArg norm hv
    _ ≤ ∑ i : Fin 3,
        ‖(PiLp.single (2 : ENNReal) i (v i) : Point3)‖ :=
      norm_sum_le _ _
    _ = ∑ i : Fin 3, |v i| := by
      apply Finset.sum_congr rfl
      intro i _
      show
        ‖(PiLp.single (2 : ENNReal) i (v i) : Point3)‖ =
          |v i|
      rw [PiLp.norm_single, Real.norm_eq_abs]
    _ ≤ ∑ _i : Fin 3, s := by
      exact Finset.sum_le_sum fun i _ => hcoord i
    _ = 3 * s := by simp

/--
Strong local overlap bound.  The lower bound is the volume of an
axis-aligned box of side `rho / 18` placed inward from `point`.
-/
theorem ordinaryTube_gridCube_overlap_volume_lower
    {rho : ℝ} (hrho : 0 < rho)
    (parent : Kakeya.DeltaTube rho)
    (cell : ℤ × ℤ × ℤ)
    {point axisPoint : Point3}
    (hpoint : point ∈ wz1PaperGridCube rho cell)
    (haxis :
      axisPoint ∈
        Kakeya.unitSegment parent.base parent.direction)
    (hnear : dist point axisPoint ≤ 5 * rho / 6) :
    ENNReal.ofReal ((rho / 18) ^ 3) ≤
      volume (wz1PaperGridCube rho cell ∩ parent.carrier) := by
  let corner : Point3 := cellCorner rho cell
  let step : ℝ := rho / 18
  let forward : Fin 3 → Prop :=
    fun i => point i ≤ corner i + rho / 2
  let lo : Fin 3 → ℝ :=
    fun i => if forward i then point i else point i - step
  let hi : Fin 3 → ℝ :=
    fun i => if forward i then point i + step else point i
  let box : Set Point3 := (WithLp.toLp 2) '' Set.Icc lo hi
  have hstep_pos : 0 < step := by
    dsimp [step]
    positivity
  have hstep_nonneg : 0 ≤ step := hstep_pos.le
  have hstep_half : step < rho / 2 := by
    dsimp [step]
    linarith
  have hpoint_bounds :
      ∀ i : Fin 3,
        corner i ≤ point i ∧ point i < corner i + rho := by
    have hbox := hpoint
    rw [wz1PaperGridCube_eq_Ico hrho cell] at hbox
    intro i
    fin_cases i
    · constructor
      · simpa [corner, cellCorner, wz1PaperGridCubeTranslation] using hbox.1
      · have h := hbox.2.1
        change point 0 < (cell.1 : ℝ) * rho + rho
        calc
          point 0 < ((cell.1 : ℝ) + 1) * rho := h
          _ = (cell.1 : ℝ) * rho + rho := by ring
    · constructor
      · simpa [corner, cellCorner, wz1PaperGridCubeTranslation] using hbox.2.2.1
      · have h := hbox.2.2.2.1
        change point 1 < (cell.2.1 : ℝ) * rho + rho
        calc
          point 1 < ((cell.2.1 : ℝ) + 1) * rho := h
          _ = (cell.2.1 : ℝ) * rho + rho := by ring
    · constructor
      · simpa [corner, cellCorner, wz1PaperGridCubeTranslation] using hbox.2.2.2.2.1
      · have h := hbox.2.2.2.2.2
        change point 2 < (cell.2.2 : ℝ) * rho + rho
        calc
          point 2 < ((cell.2.2 : ℝ) + 1) * rho := h
          _ = (cell.2.2 : ℝ) * rho + rho := by ring
  have hlohi : ∀ i, lo i ≤ hi i := by
    intro i
    by_cases hforward : forward i
    · simp [lo, hi, hforward, hstep_nonneg]
    · simp [lo, hi, hforward, hstep_nonneg]
  have hbox_subset :
      box ⊆ wz1PaperGridCube rho cell ∩ parent.carrier := by
    intro z hz
    rcases hz with ⟨zfun, hzfun, rfl⟩
    have hzlo : lo ≤ zfun := hzfun.1
    have hzhi : zfun ≤ hi := hzfun.2
    have hz_cube : WithLp.toLp 2 zfun ∈ wz1PaperGridCube rho cell := by
      rw [wz1PaperGridCube_eq_Ico hrho cell]
      have hcoord :
          ∀ i : Fin 3,
            corner i ≤ (WithLp.toLp 2 zfun) i ∧
              (WithLp.toLp 2 zfun) i < corner i + rho := by
        intro i
        have hzlo_i := hzlo i
        have hzhi_i := hzhi i
        have hp := hpoint_bounds i
        by_cases hforward : forward i
        · have hf : point i ≤ corner i + rho / 2 := hforward
          simp only [lo, hi, hforward, if_true] at hzlo_i hzhi_i
          constructor
          · exact hp.1.trans hzlo_i
          · change zfun i < corner i + rho
            calc
              zfun i ≤ point i + step := hzhi_i
              _ ≤ corner i + rho / 2 + step := by linarith
              _ < corner i + rho := by linarith
        · have hf : corner i + rho / 2 < point i :=
            lt_of_not_ge hforward
          simp only [lo, hi, hforward, if_false] at hzlo_i hzhi_i
          constructor
          · change corner i ≤ zfun i
            exact (calc
              corner i < point i - step := by linarith
              _ ≤ zfun i := hzlo_i).le
          · change zfun i < corner i + rho
            exact hzhi_i.trans_lt hp.2
      have h0 := hcoord (0 : Fin 3)
      have h1 := hcoord (1 : Fin 3)
      have h2 := hcoord (2 : Fin 3)
      constructor
      · simpa [corner, cellCorner, wz1PaperGridCubeTranslation] using h0.1
      constructor
      · change zfun 0 < ((cell.1 : ℝ) + 1) * rho
        calc
          zfun 0 < corner 0 + rho := by simpa using h0.2
          _ = ((cell.1 : ℝ) + 1) * rho := by
            simp [corner, cellCorner, wz1PaperGridCubeTranslation]
            ring
      constructor
      · simpa [corner, cellCorner, wz1PaperGridCubeTranslation] using h1.1
      constructor
      · change zfun 1 < ((cell.2.1 : ℝ) + 1) * rho
        calc
          zfun 1 < corner 1 + rho := by simpa using h1.2
          _ = ((cell.2.1 : ℝ) + 1) * rho := by
            simp [corner, cellCorner, wz1PaperGridCubeTranslation]
            ring
      constructor
      · simpa [corner, cellCorner, wz1PaperGridCubeTranslation] using h2.1
      · change zfun 2 < ((cell.2.2 : ℝ) + 1) * rho
        calc
          zfun 2 < corner 2 + rho := by simpa using h2.2
          _ = ((cell.2.2 : ℝ) + 1) * rho := by
            simp [corner, cellCorner, wz1PaperGridCubeTranslation]
            ring
    have hcoord_step :
        ∀ i : Fin 3,
          |(WithLp.toLp 2 zfun - point) i| ≤ step := by
      intro i
      have hzlo_i := hzlo i
      have hzhi_i := hzhi i
      by_cases hforward : forward i
      · simp only [lo, hi, hforward, if_true] at hzlo_i hzhi_i
        change |zfun i - point i| ≤ step
        rw [abs_le]
        constructor <;> linarith
      · simp only [lo, hi, hforward, if_false] at hzlo_i hzhi_i
        change |zfun i - point i| ≤ step
        rw [abs_le]
        constructor <;> linarith
    have hdist_point :
        dist (WithLp.toLp 2 zfun) point ≤ rho / 6 := by
      rw [dist_eq_norm]
      have hnorm :=
        norm_le_three_mul_of_coordinate_abs_le hstep_nonneg hcoord_step
      calc
        ‖WithLp.toLp 2 zfun - point‖ ≤ 3 * step := hnorm
        _ = rho / 6 := by
          dsimp [step]
          ring
    have hdist_axis :
        dist (WithLp.toLp 2 zfun) axisPoint ≤ rho := by
      calc
        dist (WithLp.toLp 2 zfun) axisPoint ≤
            dist (WithLp.toLp 2 zfun) point +
              dist point axisPoint :=
          dist_triangle _ _ _
        _ ≤ rho / 6 + 5 * rho / 6 := by linarith
        _ = rho := by ring
    exact
      ⟨hz_cube,
        Metric.mem_cthickening_of_dist_le
          (WithLp.toLp 2 zfun) axisPoint rho
          (Kakeya.unitSegment parent.base parent.direction)
          haxis hdist_axis⟩
  have hvolume_box :
      volume box = ENNReal.ofReal ((rho / 18) ^ 3) := by
    rw [volume_closedBox_three lo hi hlohi]
    have hside : ∀ i : Fin 3, hi i - lo i = step := by
      intro i
      by_cases hforward : forward i
      · simp [lo, hi, hforward]
      · simp [lo, hi, hforward]
    rw [hside 0, hside 1, hside 2]
    dsimp [step]
    ring_nf
  rw [← hvolume_box]
  exact measure_mono hbox_subset

/--
Strong-margin overlap bound used by exact coarse re-entry.

If the witnessed point is within `rho / 10` of the parent axis segment, an
inward axis-aligned box of side `rho / 4` lies in both the grid cube and the
ordinary tube.
-/
theorem ordinaryTube_gridCube_overlap_volume_lower_strong
    {rho : ℝ} (hrho : 0 < rho)
    (parent : Kakeya.DeltaTube rho)
    (cell : ℤ × ℤ × ℤ)
    {point axisPoint : Point3}
    (hpoint : point ∈ wz1PaperGridCube rho cell)
    (haxis :
      axisPoint ∈
        Kakeya.unitSegment parent.base parent.direction)
    (hnear : dist point axisPoint ≤ rho / 10) :
    ENNReal.ofReal ((1 / 100 : ℝ) * rho ^ 3) ≤
      volume (wz1PaperGridCube rho cell ∩ parent.carrier) := by
  let corner : Point3 := cellCorner rho cell
  let step : ℝ := rho / 4
  let forward : Fin 3 → Prop :=
    fun i => point i ≤ corner i + rho / 2
  let lo : Fin 3 → ℝ :=
    fun i => if forward i then point i else point i - step
  let hi : Fin 3 → ℝ :=
    fun i => if forward i then point i + step else point i
  let box : Set Point3 := (WithLp.toLp 2) '' Set.Icc lo hi
  have hstep_pos : 0 < step := by
    dsimp [step]
    positivity
  have hstep_nonneg : 0 ≤ step := hstep_pos.le
  have hstep_half : step < rho / 2 := by
    dsimp [step]
    linarith
  have hpoint_bounds :
      ∀ i : Fin 3,
        corner i ≤ point i ∧ point i < corner i + rho := by
    have hbox := hpoint
    rw [wz1PaperGridCube_eq_Ico hrho cell] at hbox
    intro i
    fin_cases i
    · constructor
      · simpa [corner, cellCorner, wz1PaperGridCubeTranslation] using hbox.1
      · have h := hbox.2.1
        change point 0 < (cell.1 : ℝ) * rho + rho
        calc
          point 0 < ((cell.1 : ℝ) + 1) * rho := h
          _ = (cell.1 : ℝ) * rho + rho := by ring
    · constructor
      · simpa [corner, cellCorner, wz1PaperGridCubeTranslation] using hbox.2.2.1
      · have h := hbox.2.2.2.1
        change point 1 < (cell.2.1 : ℝ) * rho + rho
        calc
          point 1 < ((cell.2.1 : ℝ) + 1) * rho := h
          _ = (cell.2.1 : ℝ) * rho + rho := by ring
    · constructor
      · simpa [corner, cellCorner, wz1PaperGridCubeTranslation] using hbox.2.2.2.2.1
      · have h := hbox.2.2.2.2.2
        change point 2 < (cell.2.2 : ℝ) * rho + rho
        calc
          point 2 < ((cell.2.2 : ℝ) + 1) * rho := h
          _ = (cell.2.2 : ℝ) * rho + rho := by ring
  have hlohi : ∀ i, lo i ≤ hi i := by
    intro i
    by_cases hforward : forward i
    · simp [lo, hi, hforward, hstep_nonneg]
    · simp [lo, hi, hforward, hstep_nonneg]
  have hbox_subset :
      box ⊆ wz1PaperGridCube rho cell ∩ parent.carrier := by
    intro z hz
    rcases hz with ⟨zfun, hzfun, rfl⟩
    have hzlo : lo ≤ zfun := hzfun.1
    have hzhi : zfun ≤ hi := hzfun.2
    have hz_cube : WithLp.toLp 2 zfun ∈ wz1PaperGridCube rho cell := by
      rw [wz1PaperGridCube_eq_Ico hrho cell]
      have hcoord :
          ∀ i : Fin 3,
            corner i ≤ (WithLp.toLp 2 zfun) i ∧
              (WithLp.toLp 2 zfun) i < corner i + rho := by
        intro i
        have hzlo_i := hzlo i
        have hzhi_i := hzhi i
        have hp := hpoint_bounds i
        by_cases hforward : forward i
        · have hf : point i ≤ corner i + rho / 2 := hforward
          simp only [lo, hi, hforward, if_true] at hzlo_i hzhi_i
          constructor
          · exact hp.1.trans hzlo_i
          · change zfun i < corner i + rho
            calc
              zfun i ≤ point i + step := hzhi_i
              _ ≤ corner i + rho / 2 + step := by linarith
              _ < corner i + rho := by linarith
        · have hf : corner i + rho / 2 < point i :=
            lt_of_not_ge hforward
          simp only [lo, hi, hforward, if_false] at hzlo_i hzhi_i
          constructor
          · change corner i ≤ zfun i
            exact (calc
              corner i < point i - step := by linarith
              _ ≤ zfun i := hzlo_i).le
          · change zfun i < corner i + rho
            exact hzhi_i.trans_lt hp.2
      have h0 := hcoord (0 : Fin 3)
      have h1 := hcoord (1 : Fin 3)
      have h2 := hcoord (2 : Fin 3)
      constructor
      · simpa [corner, cellCorner, wz1PaperGridCubeTranslation] using h0.1
      constructor
      · change zfun 0 < ((cell.1 : ℝ) + 1) * rho
        calc
          zfun 0 < corner 0 + rho := by simpa using h0.2
          _ = ((cell.1 : ℝ) + 1) * rho := by
            simp [corner, cellCorner, wz1PaperGridCubeTranslation]
            ring
      constructor
      · simpa [corner, cellCorner, wz1PaperGridCubeTranslation] using h1.1
      constructor
      · change zfun 1 < ((cell.2.1 : ℝ) + 1) * rho
        calc
          zfun 1 < corner 1 + rho := by simpa using h1.2
          _ = ((cell.2.1 : ℝ) + 1) * rho := by
            simp [corner, cellCorner, wz1PaperGridCubeTranslation]
            ring
      constructor
      · simpa [corner, cellCorner, wz1PaperGridCubeTranslation] using h2.1
      · change zfun 2 < ((cell.2.2 : ℝ) + 1) * rho
        calc
          zfun 2 < corner 2 + rho := by simpa using h2.2
          _ = ((cell.2.2 : ℝ) + 1) * rho := by
            simp [corner, cellCorner, wz1PaperGridCubeTranslation]
            ring
    have hcoord_step :
        ∀ i : Fin 3,
          |(WithLp.toLp 2 zfun - point) i| ≤ step := by
      intro i
      have hzlo_i := hzlo i
      have hzhi_i := hzhi i
      by_cases hforward : forward i
      · simp only [lo, hi, hforward, if_true] at hzlo_i hzhi_i
        change |zfun i - point i| ≤ step
        rw [abs_le]
        constructor <;> linarith
      · simp only [lo, hi, hforward, if_false] at hzlo_i hzhi_i
        change |zfun i - point i| ≤ step
        rw [abs_le]
        constructor <;> linarith
    have hdist_point :
        dist (WithLp.toLp 2 zfun) point ≤ 3 * rho / 4 := by
      rw [dist_eq_norm]
      have hnorm :=
        norm_le_three_mul_of_coordinate_abs_le hstep_nonneg hcoord_step
      calc
        ‖WithLp.toLp 2 zfun - point‖ ≤ 3 * step := hnorm
        _ = 3 * rho / 4 := by
          dsimp [step]
          ring
    have hdist_axis :
        dist (WithLp.toLp 2 zfun) axisPoint ≤ rho := by
      calc
        dist (WithLp.toLp 2 zfun) axisPoint ≤
            dist (WithLp.toLp 2 zfun) point +
              dist point axisPoint :=
          dist_triangle _ _ _
        _ ≤ 3 * rho / 4 + rho / 10 := by linarith
        _ ≤ rho := by linarith
    exact
      ⟨hz_cube,
        Metric.mem_cthickening_of_dist_le
          (WithLp.toLp 2 zfun) axisPoint rho
          (Kakeya.unitSegment parent.base parent.direction)
          haxis hdist_axis⟩
  have hvolume_box :
      volume box = ENNReal.ofReal ((rho / 4) ^ 3) := by
    rw [volume_closedBox_three lo hi hlohi]
    have hside : ∀ i : Fin 3, hi i - lo i = step := by
      intro i
      by_cases hforward : forward i
      · simp [lo, hi, hforward]
      · simp [lo, hi, hforward]
    rw [hside 0, hside 1, hside 2]
    dsimp [step]
    ring_nf
  calc
    ENNReal.ofReal ((1 / 100 : ℝ) * rho ^ 3) ≤
        ENNReal.ofReal ((rho / 4) ^ 3) := by
      apply ENNReal.ofReal_mono
      have rhoCube : 0 ≤ rho ^ 3 := by positivity
      calc
        (1 / 100 : ℝ) * rho ^ 3 ≤
            (1 / 64 : ℝ) * rho ^ 3 := by
          gcongr
          norm_num
        _ = (rho / 4) ^ 3 := by ring
    _ = volume box := hvolume_box.symm
    _ ≤ volume (wz1PaperGridCube rho cell ∩ parent.carrier) :=
      measure_mono hbox_subset

/--
An explicit coarse constant version of
`ordinaryTube_gridCube_overlap_volume_lower`.
-/
theorem ordinaryTube_gridCube_overlap_volume_lower_absolute
    {rho : ℝ} (hrho : 0 < rho)
    (parent : Kakeya.DeltaTube rho)
    (cell : ℤ × ℤ × ℤ)
    {point axisPoint : Point3}
    (hpoint : point ∈ wz1PaperGridCube rho cell)
    (haxis :
      axisPoint ∈
        Kakeya.unitSegment parent.base parent.direction)
    (hnear : dist point axisPoint ≤ 5 * rho / 6) :
    ENNReal.ofReal ((1 / 100000 : ℝ) * rho ^ 3) ≤
      volume (wz1PaperGridCube rho cell ∩ parent.carrier) := by
  refine
    (ENNReal.ofReal_le_ofReal ?_).trans
      (ordinaryTube_gridCube_overlap_volume_lower
        hrho parent cell hpoint haxis hnear)
  have hrho_cube : 0 ≤ rho ^ 3 := by positivity
  calc
    (1 / 100000 : ℝ) * rho ^ 3 ≤
        (1 / 5832 : ℝ) * rho ^ 3 := by
      gcongr
      norm_num
    _ = (rho / 18) ^ 3 := by ring

/--
Existential-witness form of the explicit local overlap bound.
-/
theorem ordinaryTube_gridCube_overlap_volume_lower_of_exists
    {rho : ℝ} (hrho : 0 < rho)
    (parent : Kakeya.DeltaTube rho)
    (cell : ℤ × ℤ × ℤ)
    {point : Point3}
    (hpoint : point ∈ wz1PaperGridCube rho cell)
    (hnear :
      ∃ axisPoint ∈
        Kakeya.unitSegment parent.base parent.direction,
        dist point axisPoint ≤ 5 * rho / 6) :
    ENNReal.ofReal ((1 / 100000 : ℝ) * rho ^ 3) ≤
      volume (wz1PaperGridCube rho cell ∩ parent.carrier) := by
  rcases hnear with ⟨axisPoint, haxis, hdist⟩
  exact ordinaryTube_gridCube_overlap_volume_lower_absolute
    hrho parent cell hpoint haxis hdist

end Kakeya.Assouad
