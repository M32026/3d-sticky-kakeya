import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperInfrastructure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Box characterization and boundary-layer estimates for paper grid cubes

Provides the half-open box characterization of `wz1PaperGridCube`,
cell-corner membership, active-cell window containment, pairwise
disjointness, and a uniform slab-volume bound used by the
boundary-cell pruning estimate.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The lower-left corner of a literal paper grid cube. -/
def cellCorner (scale : ℝ) (cell : ℤ × ℤ × ℤ) : Point3 :=
  wz1PaperGridCubeTranslation scale cell

/-- The lower-left corner belongs to its grid cube. -/
lemma cellCorner_mem_gridCube
    {scale : ℝ} (hscale : 0 < scale)
    (cell : ℤ × ℤ × ℤ) :
    cellCorner scale cell ∈ wz1PaperGridCube scale cell := by
  let p := cellCorner scale cell
  have h0 : p 0 = (cell.1 : ℝ) * scale := by rfl
  have h1 : p 1 = (cell.2.1 : ℝ) * scale := by rfl
  have h2 : p 2 = (cell.2.2 : ℝ) * scale := by rfl
  have h_floor0 : ⌊p 0 / scale⌋ = cell.1 := by
    rw [h0]
    have hdiv : ((cell.1 : ℝ) * scale) / scale = (cell.1 : ℝ) := by
      field_simp [hscale.ne']
    rw [hdiv]
    exact Int.floor_intCast cell.1
  have h_floor1 : ⌊p 1 / scale⌋ = cell.2.1 := by
    rw [h1]
    have hdiv : ((cell.2.1 : ℝ) * scale) / scale = (cell.2.1 : ℝ) := by
      field_simp [hscale.ne']
    rw [hdiv]
    exact Int.floor_intCast cell.2.1
  have h_floor2 : ⌊p 2 / scale⌋ = cell.2.2 := by
    rw [h2]
    have hdiv : ((cell.2.2 : ℝ) * scale) / scale = (cell.2.2 : ℝ) := by
      field_simp [hscale.ne']
    rw [hdiv]
    exact Int.floor_intCast cell.2.2
  have hindex : wz1PaperGridIndex scale p = cell := by
    simp [wz1PaperGridIndex, gridIndex, h_floor0, h_floor1, h_floor2]
  exact (mem_wz1PaperGridCube scale cell p).mpr hindex

/--
A literal paper grid cube is the half-open axis-aligned box
`[i*scale, (i+1)*scale) × [j*scale, (j+1)*scale) × [k*scale, (k+1)*scale)`.
-/
lemma wz1PaperGridCube_eq_Ico
    {scale : ℝ} (hscale : 0 < scale)
    (cell : ℤ × ℤ × ℤ) :
    wz1PaperGridCube scale cell =
    {p : Point3 |
      (cell.1 : ℝ) * scale ≤ p 0 ∧ p 0 < ((cell.1 : ℝ) + 1) * scale ∧
      (cell.2.1 : ℝ) * scale ≤ p 1 ∧ p 1 < ((cell.2.1 : ℝ) + 1) * scale ∧
      (cell.2.2 : ℝ) * scale ≤ p 2 ∧ p 2 < ((cell.2.2 : ℝ) + 1) * scale} := by
  ext p
  have h_coord : ∀ (z : ℤ) (x : ℝ), ⌊x / scale⌋ = z ↔
      (z : ℝ) * scale ≤ x ∧ x < ((z : ℝ) + 1) * scale := by
    intro z x
    rw [Int.floor_eq_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : (z : ℝ) * scale ≤ x := by
        calc
          (z : ℝ) * scale ≤ (x / scale) * scale := by gcongr
          _ = x := by field_simp [hscale.ne'] <;> ring
      have h2' : x < ((z : ℝ) + 1) * scale := by
        calc
          x = (x / scale) * scale := by field_simp [hscale.ne'] <;> ring
          _ < ((z : ℝ) + 1) * scale := by gcongr
      exact ⟨h1', h2'⟩
    · rintro ⟨h1, h2⟩
      have h1' : (z : ℝ) ≤ x / scale := by
        calc
          (z : ℝ) = (z : ℝ) * scale / scale := by
            field_simp [hscale.ne'] <;> ring
          _ ≤ x / scale := by gcongr
      have h2' : x / scale < (z : ℝ) + 1 := by
        calc
          x / scale < (((z : ℝ) + 1) * scale) / scale := by gcongr
          _ = (z : ℝ) + 1 := by field_simp [hscale.ne'] <;> ring
      exact ⟨h1', h2'⟩
  have h₁ := h_coord cell.1 (p 0)
  have h₂ := h_coord cell.2.1 (p 1)
  have h₃ := h_coord cell.2.2 (p 2)
  have h_main :
      (⌊p 0 / scale⌋ = cell.1 ∧
        ⌊p 1 / scale⌋ = cell.2.1 ∧
        ⌊p 2 / scale⌋ = cell.2.2) ↔
      ((cell.1 : ℝ) * scale ≤ p 0 ∧
        p 0 < ((cell.1 : ℝ) + 1) * scale ∧
        (cell.2.1 : ℝ) * scale ≤ p 1 ∧
        p 1 < ((cell.2.1 : ℝ) + 1) * scale ∧
        (cell.2.2 : ℝ) * scale ≤ p 2 ∧
        p 2 < ((cell.2.2 : ℝ) + 1) * scale) := by
    constructor
    · rintro ⟨ha, hb, hc⟩
      have ha' := h₁.mp ha
      have hb' := h₂.mp hb
      have hc' := h₃.mp hc
      exact ⟨ha'.1, ha'.2, hb'.1, hb'.2, hc'.1, hc'.2⟩
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      have h1' := h₁.mpr ⟨h1, h2⟩
      have h2' := h₂.mpr ⟨h3, h4⟩
      have h3' := h₃.mpr ⟨h5, h6⟩
      exact ⟨h1', h2', h3'⟩
  have h_tuple :
      (⌊p 0 / scale⌋, ⌊p 1 / scale⌋, ⌊p 2 / scale⌋) = cell ↔
        (⌊p 0 / scale⌋ = cell.1 ∧
          ⌊p 1 / scale⌋ = cell.2.1 ∧
          ⌊p 2 / scale⌋ = cell.2.2) := by
    simp [Prod.ext_iff]
    <;> tauto
  simpa [wz1PaperGridCube, wz1PaperGridIndex, gridIndex] using
    h_tuple.trans h_main

/--
Active cells of a cubical paper shading are contained in the
cropped paper window `[-1,1]^3`.
-/
lemma wz1PaperActiveCell_subset_axisBox
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hdelta : 0 < delta)
    {cell : ℤ × ℤ × ℤ}
    (hcell : cell ∈ wz1PaperActiveCells shading hdelta) :
    wz1PaperGridCube delta cell ⊆
      Kakeya.Streamlined.axisBox 2 2 2 := by
  have hunion_subset :
      shading.union ⊆ Kakeya.Streamlined.axisBox 2 2 2 := by
    intro p hp
    rcases hp with ⟨index, hpoint⟩
    let body := (wz1PaperBodyFamily fine).body index
    have h₁ : shading.carrier index ⊆ body.carrier :=
      shading.subset_body index
    have h₂ : p ∈ body.carrier := h₁ hpoint
    have h₃ : body.carrier =
        wz1PaperTubeCarrier (fine.tube index) := by rfl
    rw [h₃] at h₂
    exact h₂.2
  have hcell_subset :
      wz1PaperGridCube delta cell ⊆ shading.union := by
    have h₄ :
        shading.union ∩ wz1PaperGridCube delta cell =
          wz1PaperGridCube delta cell :=
      hcubical.inter_activeCell_eq hdelta hcell
    exact Set.inter_eq_right.mp h₄
  exact Set.Subset.trans hcell_subset hunion_subset

/--
Volume of an axis-parallel slab inside `[-1,1]^3`:
`volume {p ∈ [-1,1]^3 | |p c - x| < w} ≤ 8 * w`.
-/
lemma boundary_slab_volume_le
    (c : Fin 3) (x w : ℝ) (hw : 0 < w) :
    volume {p : Point3 |
      p ∈ Kakeya.Streamlined.axisBox 2 2 2 ∧ |p c - x| < w} ≤
      ENNReal.ofReal (8 * w) := by
  let lower : Fin 3 → ℝ := fun i => if i = c then x - w else -1
  let upper : Fin 3 → ℝ := fun i => if i = c then x + w else 1
  let S : Set (Fin 3 → ℝ) := Set.Icc lower upper
  let toLp : (Fin 3 → ℝ) → Point3 := WithLp.toLp 2
  have hsubset :
      {p : Point3 |
        p ∈ Kakeya.Streamlined.axisBox 2 2 2 ∧ |p c - x| < w} ⊆
        toLp '' S := by
    intro p hp
    have hab : p ∈ Kakeya.Streamlined.axisBox 2 2 2 := hp.1
    have hslab : |p c - x| < w := hp.2
    let y : Fin 3 → ℝ := p.ofLp
    have hy_eq : ∀ i, y i = p i := by intro i; rfl
    have hbox : |p 0| ≤ 1 ∧ |p 1| ≤ 1 ∧ |p 2| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hab
    have habs : ∀ i, |p i| ≤ 1 := by
      intro i
      fin_cases i <;> tauto
    have h_lo : lower ≤ y := by
      intro i
      by_cases hi : i = c
      · have h_i_c : i = c := hi
        have h_lower_i : lower i = x - w := by
          rw [h_i_c] <;> simp [lower]
        rw [h_lower_i, hy_eq i]
        have h : x - w ≤ p c := by
          rw [abs_lt] at hslab <;> linarith
        rw [← h_i_c] at h
        exact h
      · have h_i_ne : i ≠ c := hi
        have h_lower_i : lower i = -1 := by
          simp [lower, h_i_ne]
        rw [h_lower_i, hy_eq i]
        have h : -1 ≤ p i := by
          have h' : |p i| ≤ 1 := habs i
          rw [abs_le] at h' <;> linarith
        exact h
    have h_hi : y ≤ upper := by
      intro i
      by_cases hi : i = c
      · have h_i_c : i = c := hi
        have h_upper_i : upper i = x + w := by
          rw [h_i_c] <;> simp [upper]
        rw [h_upper_i, hy_eq i]
        have h : p c ≤ x + w := by
          rw [abs_lt] at hslab <;> linarith
        rw [← h_i_c] at h
        exact h
      · have h_i_ne : i ≠ c := hi
        have h_upper_i : upper i = 1 := by
          simp [upper, h_i_ne]
        rw [h_upper_i, hy_eq i]
        have h : p i ≤ 1 := by
          have h' : |p i| ≤ 1 := habs i
          rw [abs_le] at h' <;> linarith
        exact h
    have h_y_in_S : y ∈ S := ⟨h_lo, h_hi⟩
    have h_eq : toLp y = p := by
      dsimp only [y, toLp]
      <;> rfl
    exact ⟨y, h_y_in_S, h_eq⟩
  have h_mp : MeasureTheory.MeasurePreserving toLp :=
    PiLp.volume_preserving_toLp (ι := Fin 3)
  have h_inj : Function.Injective toLp := by
    intro a b h
    simpa [toLp, WithLp.toLp_injective] using h
  have h_cont : Continuous toLp :=
    PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)
  have h_meas : Measurable toLp := h_cont.measurable
  have h_S_meas : MeasurableSet S := measurableSet_Icc
  have h_img_meas : MeasurableSet (toLp '' S) := by
    have h : toLp '' S = (fun x : Point3 => x.ofLp) ⁻¹' S := by
      ext y
      simp only [toLp, Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa [WithLp.ofLp_toLp] using hx
      · intro hy
        refine ⟨y.ofLp, hy, ?_⟩
        simp [WithLp.ofLp_toLp]
    rw [h]
    have h_cont2 : Continuous (fun x : Point3 => x.ofLp) :=
      PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin 3 => ℝ)
    exact h_cont2.measurable h_S_meas
  have h_map :
      MeasureTheory.Measure.map toLp MeasureTheory.volume =
        MeasureTheory.volume :=
    h_mp.map_eq
  have h_vol1 : volume (toLp '' S) = volume S := by
    calc
      volume (toLp '' S) =
          MeasureTheory.Measure.map toLp volume (toLp '' S) := by
            rw [h_map]
      _ = volume (toLp ⁻¹' (toLp '' S)) :=
        MeasureTheory.Measure.map_apply h_meas h_img_meas
      _ = volume S := by rw [Set.preimage_image_eq S h_inj]
  have h_pi :
      volume S =
        ∏ i : Fin 3, ENNReal.ofReal (upper i - lower i) :=
    Real.volume_Icc_pi
  have h_main :
      volume {p : Point3 |
        p ∈ Kakeya.Streamlined.axisBox 2 2 2 ∧ |p c - x| < w} ≤
        volume (toLp '' S) :=
    measure_mono hsubset
  rw [h_vol1, h_pi] at h_main
  have h_c_val : upper c - lower c = 2 * w := by
    simp [upper, lower] <;> ring
  have h_other_val :
      ∀ i, i ≠ c → upper i - lower i = 2 := by
    intro i hi
    simp [upper, lower, hi] <;> ring
  have h_card : (Finset.univ.erase c).card = 2 := by
    simp [Finset.card_erase_of_mem (Finset.mem_univ c)] <;> decide
  have h_prod_erase :
      ∏ i ∈ Finset.univ.erase c,
          ENNReal.ofReal (upper i - lower i) =
        ENNReal.ofReal 4 := by
    have h_all :
        ∀ i ∈ Finset.univ.erase c, upper i - lower i = 2 := by
      intro i hi
      exact h_other_val i (Finset.mem_erase.mp hi |>.1)
    have h_eq :
        ∏ i ∈ Finset.univ.erase c,
            ENNReal.ofReal (upper i - lower i) =
          ∏ i ∈ Finset.univ.erase c, ENNReal.ofReal 2 := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [h_all i hi]
    rw [h_eq, Finset.prod_const, h_card]
    <;> norm_num
  have h_prod_erase_mul :
      (∏ i ∈ Finset.univ.erase c,
          ENNReal.ofReal (upper i - lower i)) *
          ENNReal.ofReal (upper c - lower c) =
        ∏ i : Fin 3, ENNReal.ofReal (upper i - lower i) :=
    Finset.prod_erase_mul (Finset.univ)
      (fun i => ENNReal.ofReal (upper i - lower i))
      (Finset.mem_univ c)
  have hprod :
      ∏ i : Fin 3, ENNReal.ofReal (upper i - lower i) =
        ENNReal.ofReal (8 * w) := by
    rw [← h_prod_erase_mul, h_prod_erase, h_c_val]
    have h_final :
        ENNReal.ofReal 4 * ENNReal.ofReal (2 * w) =
          ENNReal.ofReal (8 * w) := by
      rw [← ENNReal.ofReal_mul (by norm_num)]
      <;> norm_num <;> ring
    exact h_final
  rw [hprod] at h_main
  exact h_main

end Kakeya.Assouad
