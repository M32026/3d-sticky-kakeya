import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingBoxPigeonholeHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingStatements
import Mathlib.Tactic

/-!
# Popular box selection for PureWZ2 mild rescaling

Adaptation of the WZ1 box pigeonhole to the PureWZ2 coordinate window [-2,2]^3.

The box half-width is chosen as `1/(9*scale)` so that after isotropic dilation
by `scale`, the zero points of tubes through the box satisfy the line class
bound `|zero_point_i| ≤ 1/3`.

Calculation: for a tube with |direction 2| ≥ 1/2 and a point p in a box
of half-width w:
  |zero_point_i| ≤ |p_i| + |p_2|/|d_2| * |d_i| ≤ w + w/(1/2) * 1 = 3w
With w = 1/(9*scale), after dilation: 3 * (scale * 1/(9*scale)) = 1/3. ✓
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Finset

/-- The PureWZ2 source coordinate window [-2,2]^3. -/
def pureWZ2SourceWindow : Set Point3 :=
  {p | ∀ i, |p i| ≤ 2}

/-- A source box intersected with the PureWZ2 source window. -/
def pureWZ2SourceBox (center halfWidth : Point3) : Set Point3 :=
  wz1AxisBox center halfWidth ∩ pureWZ2SourceWindow

/-- Snap a grid-aligned coordinate to within [-2,2].

If `x` is already in [-2,2], keep it. Otherwise snap to `floor(2/δ)*δ`
or `ceil(-2/δ)*δ`, which are the nearest grid points inside the boundary.
The interval `[x-w, x+w] ∩ [-2,2]` is contained in `[y-w, y+w]` when `w ≥ δ`.
-/
lemma grid_adjust1D
    (delta : ℝ) (hdelta_pos : 0 < delta)
    (w : ℝ) (hw : delta ≤ w)
    (x : ℝ) (n : ℤ) (hx : x = (n : ℝ) * delta) :
    ∃ (y : ℝ), (∃ (m : ℤ), y = (m : ℝ) * delta) ∧ |y| ≤ 2 ∧
      Set.Icc (x - w) (x + w) ∩ Set.Icc (-2 : ℝ) 2 ⊆ Set.Icc (y - w) (y + w) := by
  by_cases h_above : x > 2
  · let m : ℤ := Int.floor (2 / delta)
    let y : ℝ := (m : ℝ) * delta
    have hpos : 0 < delta := hdelta_pos
    have hy1 : y ≤ 2 := by
      simp only [y]
      have h : (m : ℝ) ≤ 2 / delta := Int.floor_le _
      calc (m : ℝ) * delta ≤ (2 / delta) * delta := by gcongr
        _ = 2 := by field_simp [hpos.ne'] <;> ring
    have hy2 : y ≥ 2 - delta := by
      simp only [y]
      have h : (2 / delta : ℝ) < (m : ℝ) + 1 := Int.lt_floor_add_one _
      have h' : (m : ℝ) > 2 / delta - 1 := by linarith
      have h'' : (m : ℝ) * delta > (2 / delta - 1) * delta := by gcongr
      have h3 : (2 / delta - 1) * delta = 2 - delta := by
        field_simp [hpos.ne'] <;> ring
      rw [h3] at h''; linarith
    have hm_nonneg : 0 ≤ m := by
      apply Int.floor_nonneg.mpr; positivity
    have h1 : -2 ≤ y := by
      have h_y_nonneg : 0 ≤ y := by
        simp only [y]; exact mul_nonneg (mod_cast hm_nonneg) hpos.le
      linarith
    have h_abs : |y| ≤ 2 := abs_le.mpr ⟨h1, hy1⟩
    have h_cover : Set.Icc (x - w) (x + w) ∩ Set.Icc (-2 : ℝ) 2 ⊆ Set.Icc (y - w) (y + w) := by
      intro z hz
      have hz1 : z ∈ Set.Icc (x - w) (x + w) := hz.1
      have hz2 : z ∈ Set.Icc (-2 : ℝ) 2 := hz.2
      have h_left : y - w ≤ z := by
        have h : y ≤ 2 := hy1
        have h' : x - w ≤ z := hz1.1
        linarith
      have h_right : z ≤ y + w := by
        have h : z ≤ 2 := hz2.2
        have h' : y ≥ 2 - delta := hy2
        linarith [hw]
      exact ⟨h_left, h_right⟩
    exact ⟨y, ⟨m, rfl⟩, h_abs, h_cover⟩
  · by_cases h_below : x < -2
    · let m : ℤ := Int.ceil (-2 / delta)
      let y : ℝ := (m : ℝ) * delta
      have hpos : 0 < delta := hdelta_pos
      have hy1 : y ≥ -2 := by
        simp only [y]
        have h : (m : ℝ) ≥ -2 / delta := Int.le_ceil _
        calc (m : ℝ) * delta ≥ (-2 / delta) * delta := by gcongr
          _ = -2 := by field_simp [hpos.ne'] <;> ring
      have hy2 : y ≤ -2 + delta := by
        simp only [y]
        have h : (m : ℝ) < -2 / delta + 1 := Int.ceil_lt_add_one _
        have h' : (m : ℝ) * delta < (-2 / delta + 1) * delta := by gcongr
        have h'' : (-2 / delta + 1) * delta = -2 + delta := by
          field_simp [hpos.ne'] <;> ring
        rw [h''] at h'; linarith
      have hm_nonpos : m ≤ 0 := by
        have h : (-2 / delta : ℝ) ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg
          · norm_num
          · positivity
        exact Int.ceil_nonpos.mpr h
      have h2 : y ≤ 2 := by
        have h_y_nonpos : y ≤ 0 := by
          simp only [y]; exact mul_nonpos_of_nonpos_of_nonneg (mod_cast hm_nonpos) hpos.le
        linarith
      have h_abs : |y| ≤ 2 := abs_le.mpr ⟨hy1, h2⟩
      have h_cover : Set.Icc (x - w) (x + w) ∩ Set.Icc (-2 : ℝ) 2 ⊆ Set.Icc (y - w) (y + w) := by
        intro z hz
        have hz1 : z ∈ Set.Icc (x - w) (x + w) := hz.1
        have hz2 : z ∈ Set.Icc (-2 : ℝ) 2 := hz.2
        have h_left : y - w ≤ z := by
          have h : y ≤ -2 + delta := hy2
          have h' : -2 ≤ z := hz2.1
          linarith [hw]
        have h_right : z ≤ y + w := by
          have h : z ≤ x + w := hz1.2
          have h' : x < -2 := h_below
          linarith
        exact ⟨h_left, h_right⟩
      exact ⟨y, ⟨m, rfl⟩, h_abs, h_cover⟩
    · have h_x1 : -2 ≤ x := by linarith
      have h_x2 : x ≤ 2 := by linarith
      have h_abs : |x| ≤ 2 := abs_le.mpr ⟨h_x1, h_x2⟩
      have h_cover : Set.Icc (x - w) (x + w) ∩ Set.Icc (-2 : ℝ) 2 ⊆ Set.Icc (x - w) (x + w) := by
        intro z hz; exact hz.1
      exact ⟨x, ⟨n, hx⟩, h_abs, h_cover⟩

/-- Round a real number to the nearest integer multiple of `delta`.

The distance from `x` to the rounded value is at most `delta / 2`.
Uses `floor(x / delta + 1/2)`, which gives the nearest integer.
-/
lemma round_to_grid (delta : ℝ) (hdelta_pos : 0 < delta) (x : ℝ) :
    ∃ (n : ℤ), |x - (n : ℝ) * delta| ≤ delta / 2 := by
  let n : ℤ := Int.floor (x / delta + 1 / 2)
  have h1 : (n : ℝ) ≤ x / delta + 1 / 2 := Int.floor_le _
  have h2 : x / delta + 1 / 2 < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have h3 : (n : ℝ) - 1 / 2 ≤ x / delta := by linarith
  have h4 : x / delta < (n : ℝ) + 1 / 2 := by linarith
  have h5 : |x / delta - (n : ℝ)| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith
  have h6 : |x - (n : ℝ) * delta| ≤ delta / 2 := by
    have h7 : x - (n : ℝ) * delta = (x / delta - (n : ℝ)) * delta := by
      field_simp [hdelta_pos.ne'] <;> ring
    rw [h7]
    have h8 : |(x / delta - (n : ℝ)) * delta| = |x / delta - (n : ℝ)| * delta := by
      rw [abs_mul, abs_of_pos hdelta_pos]
    rw [h8]
    have h9 : |x / delta - (n : ℝ)| * delta ≤ (1 / 2 : ℝ) * delta := by gcongr
    linarith
  exact ⟨n, h6⟩

/--
Box pigeonhole on [-2,2]^3.

Partitions the source window into axis-parallel boxes of half-width `h/2`
and finds one containing at least `h^3 / 125` of the total mass.

The constant 125 is a safe overestimate of `(4+1)^3 = 125` for the
number of boxes per dimension when `h ≤ 1`.
-/
theorem pureWZ2_box_pigeonhole
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (hUnion : Y.union ⊆ pureWZ2SourceWindow)
    (h : ℝ) (hh : 0 < h) (hh2 : h ≤ 1) :
    ∃ center : Point3,
      center ∈ pureWZ2SourceWindow ∧
      ENNReal.ofReal (h ^ 3 / 125) * Y.mass ≤
        ∑ i, volume (Y.carrier i ∩ pureWZ2SourceBox center (point3 (h / 2) (h / 2) (h / 2))) := by
  let n : ℕ := Nat.floor (5 / h)
  have h_pos : 0 ≤ 5 / h := by positivity
  have h2 : 5 ≤ 5 / h := by
    calc
      5 = 5 * h / h := by field_simp [hh.ne']
      _ ≤ 5 / h := by gcongr <;> linarith
  have hn3 : n ≥ 5 := by
    exact (Nat.le_floor_iff h_pos).mpr h2
  have hN : (n : ℝ) ≤ 5 / h := Nat.floor_le h_pos
  have h_nh1 : 5 / h < (n : ℝ) + 1 := Nat.lt_floor_add_one (5 / h)
  have hnh : (n : ℝ) * h > 4 := by
    have h3 : 5 < ((n : ℝ) + 1) * h := by
      calc
        5 = (5 / h) * h := by field_simp [hh.ne']
        _ < ((n : ℝ) + 1) * h := by gcongr
    have h4 : ((n : ℝ) + 1) * h = (n : ℝ) * h + h := by ring
    rw [h4] at h3
    linarith
  set d : ℝ := (4 - h) / ((n : ℝ) - 1) with hd_def
  have hnd_pos : 0 < (n : ℝ) - 1 := by linarith
  have hd_pos : 0 < d := by
    have htwo_sub : 0 < 4 - h := by linarith
    rw [hd_def]; positivity
  have hd_le_h : d ≤ h := by
    rw [hd_def]
    have h4 : 4 - h ≤ ((n : ℝ) - 1) * h := by
      have h5 : (n : ℝ) * h > 4 := hnh
      linarith
    have h5 : (4 - h) / ((n : ℝ) - 1) ≤ (((n : ℝ) - 1) * h) / ((n : ℝ) - 1) := by
      gcongr
    have h6 : (((n : ℝ) - 1) * h) / ((n : ℝ) - 1) = h := by
      field_simp [hnd_pos.ne'] <;> ring
    exact h5.trans (by rw [h6])
  let first : Fin n := ⟨0, by omega⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  let c : Fin n → ℝ := fun k => -2 + h / 2 + (k : ℝ) * d
  have hc0 : c first = -2 + h / 2 := by simp [c, first]
  have hc_last : c last = 2 - h / 2 := by
    have h_last_val : (last : ℝ) = (n : ℝ) - 1 := by
      have hlast : (last : ℕ) = n - 1 := by simp [last]
      rw [show (last : ℝ) = ↑(last : ℕ) by simp, hlast]
      rw [Nat.cast_sub (show 1 ≤ n by omega)]; simp
    rw [show c last = -2 + h / 2 + (last : ℝ) * d by rfl]
    rw [h_last_val, hd_def]
    field_simp [hnd_pos.ne'] <;> ring
  have hc_mem : ∀ k : Fin n, c k ∈ Set.Icc (-2 : ℝ) 2 := by
    intro k
    have hk_nonneg : 0 ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k.val
    have hk_le : (k : ℝ) ≤ (n : ℝ) - 1 := by
      have hk : k.val + 1 ≤ n := by omega
      have hk' : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hk
      linarith
    have hc_lower : -2 ≤ c k := by
      have hnonneg : 0 ≤ (k : ℝ) * d := by positivity
      change -2 ≤ -2 + h / 2 + (k : ℝ) * d; linarith
    have hc_upper : c k ≤ 2 := by
      have hmul : (k : ℝ) * d ≤ ((n : ℝ) - 1) * d := mul_le_mul_of_nonneg_right hk_le hd_pos.le
      have htotal : ((n : ℝ) - 1) * d = 4 - h := by
        rw [hd_def]; field_simp [hnd_pos.ne'] <;> ring
      rw [htotal] at hmul
      change -2 + h / 2 + (k : ℝ) * d ≤ 2; linarith
    exact ⟨hc_lower, hc_upper⟩
  have h1D_cover : ∀ x : ℝ, x ∈ Set.Icc (-2 : ℝ) 2 → ∃ k : Fin n, |x - c k| ≤ h / 2 := by
    intro x hx
    let S : Finset (Fin n) := Finset.univ.filter (fun k => x ≤ c k + h / 2)
    have hS_nonempty : S.Nonempty := by
      have hx_last : x ≤ c last + h / 2 := by rw [hc_last]; linarith [hx.2]
      exact ⟨last, by simp [S, hx_last]⟩
    let k : Fin n := S.min' hS_nonempty
    have hkS : k ∈ S := Finset.min'_mem S hS_nonempty
    have hk_cond : x ≤ c k + h / 2 := by simpa [S, Finset.mem_filter] using hkS
    by_cases hk_zero : k.val = 0
    · have hk_first : k = first := by apply Fin.ext; simp [first, hk_zero]
      rw [hk_first] at hk_cond
      refine ⟨first, ?_⟩
      rw [abs_le]
      have hleft : c first - h / 2 ≤ x := by rw [hc0]; linarith [hx.1]
      constructor <;> linarith
    · have hk_pos : 0 < k.val := by omega
      let k' : Fin n := ⟨k.val - 1, by omega⟩
      have hk'_lt : k' < k := by simp [k', Fin.lt_def]; omega
      have hk'_notS : k' ∉ S := by
        intro hk'
        have hle : k ≤ k' := Finset.min'_le S k' hk'
        exact not_le.mpr hk'_lt hle
      have hk'_right : c k' + h / 2 < x := by
        have hnot : ¬x ≤ c k' + h / 2 := by simpa [S, Finset.mem_filter] using hk'_notS
        linarith
      have hk_diff : (k : ℝ) = (k' : ℝ) + 1 := by
        have hval : k.val = k'.val + 1 := by simp [k']; omega
        exact_mod_cast hval
      have hc_step : c k = c k' + d := by
        change -2 + h / 2 + (k : ℝ) * d = (-2 + h / 2 + (k' : ℝ) * d) + d
        rw [hk_diff]; ring
      have hleft : c k - h / 2 ≤ x := by rw [hc_step]; linarith [hd_le_h]
      refine ⟨k, ?_⟩
      rw [abs_le]; constructor <;> linarith
  let halfWidth : Point3 := point3 (h / 2) (h / 2) (h / 2)
  let Idx := Fin n × Fin n × Fin n
  let center : Idx → Point3 := fun p => point3 (c p.1) (c p.2.1) (c p.2.2)
  let box : Idx → Set Point3 := fun p => pureWZ2SourceBox (center p) halfWidth
  have h3D_cover : pureWZ2SourceWindow ⊆ ⋃ p : Idx, box p := by
    intro x hx
    have hx_coords : ∀ i : Fin 3, |x i| ≤ 2 := by
      simpa [pureWZ2SourceWindow, Set.mem_setOf_eq] using hx
    have hcoordinate : ∀ j : Fin 3, ∃ k : Fin n, |x j - c k| ≤ h / 2 := by
      intro j; exact h1D_cover (x j) (abs_le.mp (hx_coords j))
    choose k0 hk0 using hcoordinate 0
    choose k1 hk1 using hcoordinate 1
    choose k2 hk2 using hcoordinate 2
    let p : Idx := (k0, k1, k2)
    have haxis : x ∈ wz1AxisBox (center p) halfWidth := by
      simp only [wz1AxisBox, Set.mem_setOf_eq]; intro i
      fin_cases i
      · simpa [center, halfWidth, point3] using hk0
      · simpa [center, halfWidth, point3] using hk1
      · simpa [center, halfWidth, point3] using hk2
    have hbox : x ∈ box p := by
      simp only [box, pureWZ2SourceBox, Set.mem_inter_iff]
      exact ⟨haxis, hx⟩
    exact Set.mem_iUnion.mpr ⟨p, hbox⟩
  have hcarrier_cover : ∀ i : Fin F.card, Y.carrier i ⊆ ⋃ p : Idx, box p := by
    intro i
    exact subset_trans (show Y.carrier i ⊆ Y.union from fun x hx => ⟨i, hx⟩) (subset_trans hUnion h3D_cover)
  have hvolume : ∀ i : Fin F.card, volume (Y.carrier i) ≤ ∑ p : Idx, volume (Y.carrier i ∩ box p) := by
    intro i; exact measure_cover_le_sum (hcarrier_cover i)
  have hsum : Y.mass ≤ ∑ p : Idx, ∑ i : Fin F.card, volume (Y.carrier i ∩ box p) := by
    calc
      Y.mass = ∑ i : Fin F.card, volume (Y.carrier i) := by rfl
      _ ≤ ∑ i, ∑ p, volume (Y.carrier i ∩ box p) := Finset.sum_le_sum (fun i _ => hvolume i)
      _ = ∑ p, ∑ i, volume (Y.carrier i ∩ box p) := by rw [Finset.sum_comm]
  let captured : Idx → ENNReal := fun p => ∑ i : Fin F.card, volume (Y.carrier i ∩ box p)
  let threshold : Idx → ENNReal := fun _ => ENNReal.ofReal (h ^ 3 / 125) * Y.mass
  have hIdx_nonempty : Nonempty Idx := ⟨(first, first, first)⟩
  have hcard : Fintype.card Idx = n ^ 3 := by
    simp [Idx, Fintype.card_prod] <;> ring
  have hthreshold_sum : ∑ p : Idx, threshold p = (Fintype.card Idx : ENNReal) * ENNReal.ofReal (h ^ 3 / 125) * Y.mass := by
    simp [threshold, Finset.sum_const, hcard] <;> ring
  have hcube : (n ^ 3 : ENNReal) * ENNReal.ofReal (h ^ 3 / 125) ≤ 1 := by
    have hn : (n : ℝ) ≤ 5 / h := hN
    have h7 : (n : ℝ) ^ 3 * (h ^ 3 / 125) ≤ 1 := by
      calc
        (n : ℝ) ^ 3 * (h ^ 3 / 125)
          ≤ (5 / h) ^ 3 * (h ^ 3 / 125) := by gcongr
        _ = 125 / h ^ 3 * (h ^ 3 / 125) := by ring
        _ = 1 := by field_simp [hh.ne'] <;> ring
    have h8 : ((n ^ 3 : ENNReal) * ENNReal.ofReal (h ^ 3 / 125)) =
        ENNReal.ofReal ((n : ℝ) ^ 3 * (h ^ 3 / 125)) := by
      simp [ENNReal.ofReal_mul]
      <;> norm_cast <;> ring
    rw [h8]
    have h9 : ENNReal.ofReal ((n : ℝ) ^ 3 * (h ^ 3 / 125)) ≤ (1 : ENNReal) := by
      rw [ENNReal.ofReal_le_one] <;> linarith
    exact h9
  have hsum_compare : ∑ p : Idx, threshold p ≤ ∑ p : Idx, captured p := by
    rw [hthreshold_sum, hcard]
    have hcast : (↑(n ^ 3) : ENNReal) = (↑n ^ 3 : ENNReal) := by rw [Nat.cast_pow]
    rw [hcast]
    exact calc
      (↑n ^ 3 : ENNReal) * ENNReal.ofReal (h ^ 3 / 125) * Y.mass
        ≤ 1 * Y.mass := by gcongr
      _ = Y.mass := by ring
      _ ≤ ∑ p : Idx, captured p := hsum
  have hexists : ∃ p : Idx, threshold p ≤ captured p := by
    simpa using ENNReal.exists_le_of_sum_le (Finset.univ_nonempty : (Finset.univ : Finset Idx).Nonempty) hsum_compare
  rcases hexists with ⟨p, hp⟩
  have hcenter : center p ∈ pureWZ2SourceWindow := by
    have hcoords : ∀ i : Fin 3, |(center p) i| ≤ 2 := by
      intro i
      fin_cases i
      · simpa [center, point3] using abs_le.mpr (hc_mem p.1)
      · simpa [center, point3] using abs_le.mpr (hc_mem p.2.1)
      · simpa [center, point3] using abs_le.mpr (hc_mem p.2.2)
    simpa [pureWZ2SourceWindow, Set.mem_setOf_eq] using hcoords
  have h_final : ENNReal.ofReal (h ^ 3 / 125) * Y.mass ≤
      ∑ i : Fin F.card, volume (Y.carrier i ∩ pureWZ2SourceBox (center p) (point3 (h / 2) (h / 2) (h / 2))) := by
    simpa [threshold, captured] using hp
  exact ⟨center p, hcenter, h_final⟩

/-- Grid-aligned box pigeonhole on [-2,2]^3.

Partitions the source window into blocks of side `K * delta` whose centers
lie at integer multiples of `delta` (requires `K` even). Finds one block
containing at least `(K*delta)^3 / 8000` of the total mass.

The grid alignment ensures that translating the configuration by `-center`
preserves `WZ1PaperIsCubicalShading` at scale `delta`.
-/
theorem pureWZ2_grid_aligned_box_pigeonhole
    {delta : ℝ} {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (hUnion : Y.union ⊆ pureWZ2SourceWindow)
    (hdelta_pos : 0 < delta)
    (K : ℕ) (hK_pos : 0 < K) (hK_even : K % 2 = 0)
    (hKdelta_le_one : (K : ℝ) * delta ≤ 1) :
    ∃ (center : Point3),
      (∀ (i : Fin 3), ∃ (n : ℤ), center i = (n : ℝ) * delta) ∧
      center ∈ pureWZ2SourceWindow ∧
      ENNReal.ofReal (((K : ℝ) * delta) ^ 3 / 8000) * Y.mass ≤
        ∑ i, MeasureTheory.volume (Y.carrier i ∩
          pureWZ2SourceBox center
            (point3 (((K : ℝ) * delta) / 2) (((K : ℝ) * delta) / 2) (((K : ℝ) * delta) / 2))) := by
  set h : ℝ := ((K : ℝ) - 1) * delta with hh_def
  have hK_ge2 : K ≥ 2 := by omega
  have hh_pos : 0 < h := by
    dsimp only [h]
    have h1 : (K : ℝ) ≥ 2 := by exact_mod_cast hK_ge2
    nlinarith
  have hh_le_one : h ≤ 1 := by
    dsimp only [h]
    nlinarith
  rcases pureWZ2_box_pigeonhole Y hUnion h hh_pos hh_le_one with ⟨c, hc_window, hmass⟩
  set w1 : ℝ := h / 2 with hw1_def
  set w2 : ℝ := (K : ℝ) * delta / 2 with hw2_def
  have hw2_ge_delta : delta ≤ w2 := by
    dsimp only [w2]
    have h1 : (K : ℝ) ≥ 2 := by exact_mod_cast hK_ge2
    nlinarith
  have hw1_plus : w1 + delta / 2 = w2 := by
    simp only [w1, w2, h] <;> ring
  -- Round each coordinate of c to the nearest δ-grid point
  rcases round_to_grid delta hdelta_pos (c 0) with ⟨n0, hn0⟩
  rcases round_to_grid delta hdelta_pos (c 1) with ⟨n1, hn1⟩
  rcases round_to_grid delta hdelta_pos (c 2) with ⟨n2, hn2⟩
  set c' : Point3 := point3 ((n0 : ℝ) * delta) ((n1 : ℝ) * delta) ((n2 : ℝ) * delta) with hc'_def
  set half1 : Point3 := point3 w1 w1 w1 with hhalf1_def
  set half2 : Point3 := point3 w2 w2 w2 with hhalf2_def
  -- The original box (half1 around c) is contained in the grid-aligned box (half2 around c')
  have hbox1_subset_box2 : wz1AxisBox c half1 ⊆ wz1AxisBox c' half2 := by
    intro p hp
    have h_def : ∀ i, |p i - c i| ≤ half1 i := by simpa [wz1AxisBox, Set.mem_setOf_eq] using hp
    have h_half10 : half1 0 = w1 := by simp [hhalf1_def, point3_apply]
    have h_half11 : half1 1 = w1 := by simp [hhalf1_def, point3_apply]
    have h_half12 : half1 2 = w1 := by simp [hhalf1_def, point3_apply]
    have h_half20 : half2 0 = w2 := by simp [hhalf2_def, point3_apply]
    have h_half21 : half2 1 = w2 := by simp [hhalf2_def, point3_apply]
    have h_half22 : half2 2 = w2 := by simp [hhalf2_def, point3_apply]
    have h_c'0 : c' 0 = (n0 : ℝ) * delta := by simp [hc'_def, point3_apply]
    have h_c'1 : c' 1 = (n1 : ℝ) * delta := by simp [hc'_def, point3_apply]
    have h_c'2 : c' 2 = (n2 : ℝ) * delta := by simp [hc'_def, point3_apply]
    simp only [wz1AxisBox, Set.mem_setOf_eq]
    intro i
    fin_cases i
    · have h_a1 : |p 0 - c 0| ≤ half1 0 := h_def 0
      have h_a : |p 0 - c 0| ≤ w1 := by rw [h_half10] at h_a1; exact h_a1
      have h_b : |c 0 - c' 0| ≤ delta / 2 := by rw [h_c'0]; exact hn0
      have h_tri : |p 0 - c' 0| ≤ w1 + delta / 2 := by
        rw [abs_le]; constructor <;> linarith [abs_le.mp h_a, abs_le.mp h_b]
      have h : |p 0 - c' 0| ≤ half2 0 := by
        have h_eq : half2 0 = w2 := h_half20
        rw [h_eq]
        rw [hw1_plus] at h_tri
        exact h_tri
      exact h
    · have h_a1 : |p 1 - c 1| ≤ half1 1 := h_def 1
      have h_a : |p 1 - c 1| ≤ w1 := by rw [h_half11] at h_a1; exact h_a1
      have h_b : |c 1 - c' 1| ≤ delta / 2 := by rw [h_c'1]; exact hn1
      have h_tri : |p 1 - c' 1| ≤ w1 + delta / 2 := by
        rw [abs_le]; constructor <;> linarith [abs_le.mp h_a, abs_le.mp h_b]
      have h : |p 1 - c' 1| ≤ half2 1 := by
        have h_eq : half2 1 = w2 := h_half21
        rw [h_eq]
        rw [hw1_plus] at h_tri
        exact h_tri
      exact h
    · have h_a1 : |p 2 - c 2| ≤ half1 2 := h_def 2
      have h_a : |p 2 - c 2| ≤ w1 := by rw [h_half12] at h_a1; exact h_a1
      have h_b : |c 2 - c' 2| ≤ delta / 2 := by rw [h_c'2]; exact hn2
      have h_tri : |p 2 - c' 2| ≤ w1 + delta / 2 := by
        rw [abs_le]; constructor <;> linarith [abs_le.mp h_a, abs_le.mp h_b]
      have h : |p 2 - c' 2| ≤ half2 2 := by
        have h_eq : half2 2 = w2 := h_half22
        rw [h_eq]
        rw [hw1_plus] at h_tri
        exact h_tri
      exact h
  -- Snap each grid-aligned coordinate to within [-2,2]
  rcases grid_adjust1D delta hdelta_pos w2 hw2_ge_delta ((n0 : ℝ) * delta) n0 rfl with ⟨y0, ⟨m0, hy0⟩, h_y0_abs, h_cover0⟩
  rcases grid_adjust1D delta hdelta_pos w2 hw2_ge_delta ((n1 : ℝ) * delta) n1 rfl with ⟨y1, ⟨m1, hy1⟩, h_y1_abs, h_cover1⟩
  rcases grid_adjust1D delta hdelta_pos w2 hw2_ge_delta ((n2 : ℝ) * delta) n2 rfl with ⟨y2, ⟨m2, hy2⟩, h_y2_abs, h_cover2⟩
  set newCenter : Point3 := point3 y0 y1 y2 with hnewCenter_def
  have hnewCenter_grid : ∀ (i : Fin 3), ∃ (n : ℤ), newCenter i = (n : ℝ) * delta := by
    intro i
    fin_cases i
    · exact ⟨m0, by simp [hnewCenter_def, point3_apply, hy0]⟩
    · exact ⟨m1, by simp [hnewCenter_def, point3_apply, hy1]⟩
    · exact ⟨m2, by simp [hnewCenter_def, point3_apply, hy2]⟩
  have hnewCenter_window : newCenter ∈ pureWZ2SourceWindow := by
    simp only [pureWZ2SourceWindow, Set.mem_setOf_eq]
    intro i
    fin_cases i
    · simpa [hnewCenter_def, point3_apply] using h_y0_abs
    · simpa [hnewCenter_def, point3_apply] using h_y1_abs
    · simpa [hnewCenter_def, point3_apply] using h_y2_abs
  -- The grid-aligned box intersected with the window is contained in the snapped box
  have hbox2_cover : wz1AxisBox c' half2 ∩ pureWZ2SourceWindow ⊆ wz1AxisBox newCenter half2 := by
    intro p hp
    have h_in_box : p ∈ wz1AxisBox c' half2 := hp.1
    have h_in_window : p ∈ pureWZ2SourceWindow := hp.2
    have h_box_def : ∀ i, |p i - c' i| ≤ half2 i := by simpa [wz1AxisBox, Set.mem_setOf_eq] using h_in_box
    have h_half20 : half2 0 = w2 := by simp [hhalf2_def, point3_apply]
    have h_half21 : half2 1 = w2 := by simp [hhalf2_def, point3_apply]
    have h_half22 : half2 2 = w2 := by simp [hhalf2_def, point3_apply]
    have h_c'0 : c' 0 = (n0 : ℝ) * delta := by simp [hc'_def, point3_apply]
    have h_c'1 : c' 1 = (n1 : ℝ) * delta := by simp [hc'_def, point3_apply]
    have h_c'2 : c' 2 = (n2 : ℝ) * delta := by simp [hc'_def, point3_apply]
    have h_new0 : newCenter 0 = y0 := by simp [hnewCenter_def, point3_apply]
    have h_new1 : newCenter 1 = y1 := by simp [hnewCenter_def, point3_apply]
    have h_new2 : newCenter 2 = y2 := by simp [hnewCenter_def, point3_apply]
    simp only [wz1AxisBox, Set.mem_setOf_eq]
    intro i
    fin_cases i
    · have h_abs1 : |p 0 - c' 0| ≤ half2 0 := h_box_def 0
      have h_abs : |p 0 - c' 0| ≤ w2 := by rw [h_half20] at h_abs1; exact h_abs1
      have h_coord : p 0 ∈ Set.Icc ((n0 : ℝ) * delta - w2) ((n0 : ℝ) * delta + w2) := by
        rw [h_c'0] at h_abs
        have h_bounds := abs_le.mp h_abs
        exact ⟨by linarith, by linarith⟩
      have h_win : p 0 ∈ Set.Icc (-2 : ℝ) 2 := abs_le.mp (h_in_window 0)
      have h4 : p 0 ∈ Set.Icc (y0 - w2) (y0 + w2) := h_cover0 ⟨h_coord, h_win⟩
      have h5 : |p 0 - newCenter 0| ≤ half2 0 := by
        rw [h_new0, h_half20]
        exact abs_le.mpr ⟨by linarith [h4.1], by linarith [h4.2]⟩
      exact h5
    · have h_abs1 : |p 1 - c' 1| ≤ half2 1 := h_box_def 1
      have h_abs : |p 1 - c' 1| ≤ w2 := by rw [h_half21] at h_abs1; exact h_abs1
      have h_coord : p 1 ∈ Set.Icc ((n1 : ℝ) * delta - w2) ((n1 : ℝ) * delta + w2) := by
        rw [h_c'1] at h_abs
        have h_bounds := abs_le.mp h_abs
        exact ⟨by linarith, by linarith⟩
      have h_win : p 1 ∈ Set.Icc (-2 : ℝ) 2 := abs_le.mp (h_in_window 1)
      have h4 : p 1 ∈ Set.Icc (y1 - w2) (y1 + w2) := h_cover1 ⟨h_coord, h_win⟩
      have h5 : |p 1 - newCenter 1| ≤ half2 1 := by
        rw [h_new1, h_half21]
        exact abs_le.mpr ⟨by linarith [h4.1], by linarith [h4.2]⟩
      exact h5
    · have h_abs1 : |p 2 - c' 2| ≤ half2 2 := h_box_def 2
      have h_abs : |p 2 - c' 2| ≤ w2 := by rw [h_half22] at h_abs1; exact h_abs1
      have h_coord : p 2 ∈ Set.Icc ((n2 : ℝ) * delta - w2) ((n2 : ℝ) * delta + w2) := by
        rw [h_c'2] at h_abs
        have h_bounds := abs_le.mp h_abs
        exact ⟨by linarith, by linarith⟩
      have h_win : p 2 ∈ Set.Icc (-2 : ℝ) 2 := abs_le.mp (h_in_window 2)
      have h4 : p 2 ∈ Set.Icc (y2 - w2) (y2 + w2) := h_cover2 ⟨h_coord, h_win⟩
      have h5 : |p 2 - newCenter 2| ≤ half2 2 := by
        rw [h_new2, h_half22]
        exact abs_le.mpr ⟨by linarith [h4.1], by linarith [h4.2]⟩
      exact h5
  -- Full inclusion: sourceBox c half1 ⊆ sourceBox newCenter half2
  have h_full_inclusion : pureWZ2SourceBox c half1 ⊆ pureWZ2SourceBox newCenter half2 := by
    intro x hx
    have h1 : x ∈ wz1AxisBox c half1 := hx.1
    have h2 : x ∈ pureWZ2SourceWindow := hx.2
    have h3 : x ∈ wz1AxisBox c' half2 := hbox1_subset_box2 h1
    have h4 : x ∈ wz1AxisBox c' half2 ∩ pureWZ2SourceWindow := ⟨h3, h2⟩
    have h5 : x ∈ wz1AxisBox newCenter half2 := hbox2_cover h4
    exact ⟨h5, h2⟩
  -- Transfer mass from the original box to the new box
  have h_mass_transfer :
      ∑ i, MeasureTheory.volume (Y.carrier i ∩ pureWZ2SourceBox c half1) ≤
      ∑ i, MeasureTheory.volume (Y.carrier i ∩ pureWZ2SourceBox newCenter half2) := by
    apply Finset.sum_le_sum
    intro i _
    have h5 : Y.carrier i ∩ pureWZ2SourceBox c half1 ⊆ Y.carrier i ∩ pureWZ2SourceBox newCenter half2 := by
      intro x hx
      exact ⟨hx.1, h_full_inclusion hx.2⟩
    exact MeasureTheory.measure_mono h5
  -- Real inequality: (Kδ)^3/8000 ≤ ((K-1)δ)^3/125 for K ≥ 2
  have h_real_ineq : ((K : ℝ) * delta) ^ 3 / 8000 ≤ h ^ 3 / 125 := by
    dsimp only [h]
    have h1 : (K : ℝ) ≥ 2 := by exact_mod_cast hK_ge2
    have h2 : 4 * ((K : ℝ) - 1) ≥ (K : ℝ) := by linarith
    have h3 : (4 * ((K : ℝ) - 1)) ^ 3 ≥ (K : ℝ) ^ 3 := by gcongr
    have h4 : 64 * (((K : ℝ) - 1) ^ 3) ≥ (K : ℝ) ^ 3 := by
      have h5 : (4 * ((K : ℝ) - 1)) ^ 3 = 64 * (((K : ℝ) - 1) ^ 3) := by ring
      linarith
    calc ((K : ℝ) * delta) ^ 3 / 8000
      = ((K : ℝ) ^ 3 * delta ^ 3) / 8000 := by ring
    _ ≤ (64 * (((K : ℝ) - 1) ^ 3) * delta ^ 3) / 8000 := by gcongr
    _ = (((K : ℝ) - 1) ^ 3 * delta ^ 3) / 125 := by ring
    _ = (((K : ℝ) - 1) * delta) ^ 3 / 125 := by ring
  have h_ennreal : ENNReal.ofReal (((K : ℝ) * delta) ^ 3 / 8000) ≤ ENNReal.ofReal (h ^ 3 / 125) :=
    ENNReal.ofReal_le_ofReal h_real_ineq
  have h_mass_compare :
      ENNReal.ofReal (((K : ℝ) * delta) ^ 3 / 8000) * Y.mass ≤
      ENNReal.ofReal (h ^ 3 / 125) * Y.mass := by
    gcongr
    <;> exact h_ennreal
  exact ⟨newCenter, hnewCenter_grid, hnewCenter_window,
    h_mass_compare.trans (hmass.trans h_mass_transfer)⟩

/-- Strong grid-aligned box pigeonhole on [-2,2]^3.

Like `pureWZ2_grid_aligned_box_pigeonhole`, but retains the stronger
mass bound `((K-1)*δ)^3 / 125` from the inner box pigeonhole. Since the
grid-aligned outer box contains the inner box, it captures at least as
much mass, so the stronger bound survives.
-/
theorem pureWZ2_grid_aligned_box_pigeonhole_strong
    {delta : ℝ} {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (hUnion : Y.union ⊆ pureWZ2SourceWindow)
    (hdelta_pos : 0 < delta)
    (K : ℕ) (hK_pos : 0 < K) (hK_even : K % 2 = 0)
    (hKdelta_le_one : (K : ℝ) * delta ≤ 1) :
    ∃ (center : Point3),
      (∀ (i : Fin 3), ∃ (n : ℤ), center i = (n : ℝ) * delta) ∧
      center ∈ pureWZ2SourceWindow ∧
      ENNReal.ofReal ((((K : ℝ) - 1) * delta) ^ 3 / 125) * Y.mass ≤
        ∑ i, MeasureTheory.volume (Y.carrier i ∩
          pureWZ2SourceBox center
            (point3 (((K : ℝ) * delta) / 2) (((K : ℝ) * delta) / 2) (((K : ℝ) * delta) / 2))) := by
  set h : ℝ := ((K : ℝ) - 1) * delta with hh_def
  have hK_ge2 : K ≥ 2 := by omega
  have hh_pos : 0 < h := by
    dsimp only [h]
    have h1 : (K : ℝ) ≥ 2 := by exact_mod_cast hK_ge2
    nlinarith
  have hh_le_one : h ≤ 1 := by
    dsimp only [h]
    nlinarith
  rcases pureWZ2_box_pigeonhole Y hUnion h hh_pos hh_le_one with ⟨c, hc_window, hmass⟩
  set w1 : ℝ := h / 2 with hw1_def
  set w2 : ℝ := (K : ℝ) * delta / 2 with hw2_def
  have hw2_ge_delta : delta ≤ w2 := by
    dsimp only [w2]
    have h1 : (K : ℝ) ≥ 2 := by exact_mod_cast hK_ge2
    nlinarith
  have hw1_plus : w1 + delta / 2 = w2 := by
    simp only [w1, w2, h] <;> ring
  rcases round_to_grid delta hdelta_pos (c 0) with ⟨n0, hn0⟩
  rcases round_to_grid delta hdelta_pos (c 1) with ⟨n1, hn1⟩
  rcases round_to_grid delta hdelta_pos (c 2) with ⟨n2, hn2⟩
  set c' : Point3 := point3 ((n0 : ℝ) * delta) ((n1 : ℝ) * delta) ((n2 : ℝ) * delta) with hc'_def
  set half1 : Point3 := point3 w1 w1 w1 with hhalf1_def
  set half2 : Point3 := point3 w2 w2 w2 with hhalf2_def
  have hbox1_subset_box2 : wz1AxisBox c half1 ⊆ wz1AxisBox c' half2 := by
    intro p hp
    have h_def : ∀ i, |p i - c i| ≤ half1 i := by simpa [wz1AxisBox, Set.mem_setOf_eq] using hp
    have h_half10 : half1 0 = w1 := by simp [hhalf1_def, point3_apply]
    have h_half11 : half1 1 = w1 := by simp [hhalf1_def, point3_apply]
    have h_half12 : half1 2 = w1 := by simp [hhalf1_def, point3_apply]
    have h_half20 : half2 0 = w2 := by simp [hhalf2_def, point3_apply]
    have h_half21 : half2 1 = w2 := by simp [hhalf2_def, point3_apply]
    have h_half22 : half2 2 = w2 := by simp [hhalf2_def, point3_apply]
    have h_c'0 : c' 0 = (n0 : ℝ) * delta := by simp [hc'_def, point3_apply]
    have h_c'1 : c' 1 = (n1 : ℝ) * delta := by simp [hc'_def, point3_apply]
    have h_c'2 : c' 2 = (n2 : ℝ) * delta := by simp [hc'_def, point3_apply]
    simp only [wz1AxisBox, Set.mem_setOf_eq]
    intro i
    fin_cases i
    · have h_a1 : |p 0 - c 0| ≤ half1 0 := h_def 0
      have h_a : |p 0 - c 0| ≤ w1 := by rw [h_half10] at h_a1; exact h_a1
      have h_b : |c 0 - c' 0| ≤ delta / 2 := by rw [h_c'0]; exact hn0
      have h_tri : |p 0 - c' 0| ≤ w1 + delta / 2 := by
        rw [abs_le]; constructor <;> linarith [abs_le.mp h_a, abs_le.mp h_b]
      have h : |p 0 - c' 0| ≤ half2 0 := by
        have h_eq : half2 0 = w2 := h_half20
        rw [h_eq]
        rw [hw1_plus] at h_tri
        exact h_tri
      exact h
    · have h_a1 : |p 1 - c 1| ≤ half1 1 := h_def 1
      have h_a : |p 1 - c 1| ≤ w1 := by rw [h_half11] at h_a1; exact h_a1
      have h_b : |c 1 - c' 1| ≤ delta / 2 := by rw [h_c'1]; exact hn1
      have h_tri : |p 1 - c' 1| ≤ w1 + delta / 2 := by
        rw [abs_le]; constructor <;> linarith [abs_le.mp h_a, abs_le.mp h_b]
      have h : |p 1 - c' 1| ≤ half2 1 := by
        have h_eq : half2 1 = w2 := h_half21
        rw [h_eq]
        rw [hw1_plus] at h_tri
        exact h_tri
      exact h
    · have h_a1 : |p 2 - c 2| ≤ half1 2 := h_def 2
      have h_a : |p 2 - c 2| ≤ w1 := by rw [h_half12] at h_a1; exact h_a1
      have h_b : |c 2 - c' 2| ≤ delta / 2 := by rw [h_c'2]; exact hn2
      have h_tri : |p 2 - c' 2| ≤ w1 + delta / 2 := by
        rw [abs_le]; constructor <;> linarith [abs_le.mp h_a, abs_le.mp h_b]
      have h : |p 2 - c' 2| ≤ half2 2 := by
        have h_eq : half2 2 = w2 := h_half22
        rw [h_eq]
        rw [hw1_plus] at h_tri
        exact h_tri
      exact h
  rcases grid_adjust1D delta hdelta_pos w2 hw2_ge_delta ((n0 : ℝ) * delta) n0 rfl with ⟨y0, ⟨m0, hy0⟩, h_y0_abs, h_cover0⟩
  rcases grid_adjust1D delta hdelta_pos w2 hw2_ge_delta ((n1 : ℝ) * delta) n1 rfl with ⟨y1, ⟨m1, hy1⟩, h_y1_abs, h_cover1⟩
  rcases grid_adjust1D delta hdelta_pos w2 hw2_ge_delta ((n2 : ℝ) * delta) n2 rfl with ⟨y2, ⟨m2, hy2⟩, h_y2_abs, h_cover2⟩
  set newCenter : Point3 := point3 y0 y1 y2 with hnewCenter_def
  have hnewCenter_grid : ∀ (i : Fin 3), ∃ (n : ℤ), newCenter i = (n : ℝ) * delta := by
    intro i
    fin_cases i
    · exact ⟨m0, by simp [hnewCenter_def, point3_apply, hy0]⟩
    · exact ⟨m1, by simp [hnewCenter_def, point3_apply, hy1]⟩
    · exact ⟨m2, by simp [hnewCenter_def, point3_apply, hy2]⟩
  have hnewCenter_window : newCenter ∈ pureWZ2SourceWindow := by
    simp only [pureWZ2SourceWindow, Set.mem_setOf_eq]
    intro i
    fin_cases i
    · simpa [hnewCenter_def, point3_apply] using h_y0_abs
    · simpa [hnewCenter_def, point3_apply] using h_y1_abs
    · simpa [hnewCenter_def, point3_apply] using h_y2_abs
  have hbox2_cover : wz1AxisBox c' half2 ∩ pureWZ2SourceWindow ⊆ wz1AxisBox newCenter half2 := by
    intro p hp
    have h_in_box : p ∈ wz1AxisBox c' half2 := hp.1
    have h_in_window : p ∈ pureWZ2SourceWindow := hp.2
    have h_box_def : ∀ i, |p i - c' i| ≤ half2 i := by simpa [wz1AxisBox, Set.mem_setOf_eq] using h_in_box
    have h_half20 : half2 0 = w2 := by simp [hhalf2_def, point3_apply]
    have h_half21 : half2 1 = w2 := by simp [hhalf2_def, point3_apply]
    have h_half22 : half2 2 = w2 := by simp [hhalf2_def, point3_apply]
    have h_c'0 : c' 0 = (n0 : ℝ) * delta := by simp [hc'_def, point3_apply]
    have h_c'1 : c' 1 = (n1 : ℝ) * delta := by simp [hc'_def, point3_apply]
    have h_c'2 : c' 2 = (n2 : ℝ) * delta := by simp [hc'_def, point3_apply]
    have h_new0 : newCenter 0 = y0 := by simp [hnewCenter_def, point3_apply]
    have h_new1 : newCenter 1 = y1 := by simp [hnewCenter_def, point3_apply]
    have h_new2 : newCenter 2 = y2 := by simp [hnewCenter_def, point3_apply]
    simp only [wz1AxisBox, Set.mem_setOf_eq]
    intro i
    fin_cases i
    · have h_abs1 : |p 0 - c' 0| ≤ half2 0 := h_box_def 0
      have h_abs : |p 0 - c' 0| ≤ w2 := by rw [h_half20] at h_abs1; exact h_abs1
      have h_coord : p 0 ∈ Set.Icc ((n0 : ℝ) * delta - w2) ((n0 : ℝ) * delta + w2) := by
        rw [h_c'0] at h_abs
        have h_bounds := abs_le.mp h_abs
        exact ⟨by linarith, by linarith⟩
      have h_win : p 0 ∈ Set.Icc (-2 : ℝ) 2 := abs_le.mp (h_in_window 0)
      have h4 : p 0 ∈ Set.Icc (y0 - w2) (y0 + w2) := h_cover0 ⟨h_coord, h_win⟩
      have h5 : |p 0 - newCenter 0| ≤ half2 0 := by
        rw [h_new0, h_half20]
        exact abs_le.mpr ⟨by linarith [h4.1], by linarith [h4.2]⟩
      exact h5
    · have h_abs1 : |p 1 - c' 1| ≤ half2 1 := h_box_def 1
      have h_abs : |p 1 - c' 1| ≤ w2 := by rw [h_half21] at h_abs1; exact h_abs1
      have h_coord : p 1 ∈ Set.Icc ((n1 : ℝ) * delta - w2) ((n1 : ℝ) * delta + w2) := by
        rw [h_c'1] at h_abs
        have h_bounds := abs_le.mp h_abs
        exact ⟨by linarith, by linarith⟩
      have h_win : p 1 ∈ Set.Icc (-2 : ℝ) 2 := abs_le.mp (h_in_window 1)
      have h4 : p 1 ∈ Set.Icc (y1 - w2) (y1 + w2) := h_cover1 ⟨h_coord, h_win⟩
      have h5 : |p 1 - newCenter 1| ≤ half2 1 := by
        rw [h_new1, h_half21]
        exact abs_le.mpr ⟨by linarith [h4.1], by linarith [h4.2]⟩
      exact h5
    · have h_abs1 : |p 2 - c' 2| ≤ half2 2 := h_box_def 2
      have h_abs : |p 2 - c' 2| ≤ w2 := by rw [h_half22] at h_abs1; exact h_abs1
      have h_coord : p 2 ∈ Set.Icc ((n2 : ℝ) * delta - w2) ((n2 : ℝ) * delta + w2) := by
        rw [h_c'2] at h_abs
        have h_bounds := abs_le.mp h_abs
        exact ⟨by linarith, by linarith⟩
      have h_win : p 2 ∈ Set.Icc (-2 : ℝ) 2 := abs_le.mp (h_in_window 2)
      have h4 : p 2 ∈ Set.Icc (y2 - w2) (y2 + w2) := h_cover2 ⟨h_coord, h_win⟩
      have h5 : |p 2 - newCenter 2| ≤ half2 2 := by
        rw [h_new2, h_half22]
        exact abs_le.mpr ⟨by linarith [h4.1], by linarith [h4.2]⟩
      exact h5
  have h_full_inclusion : pureWZ2SourceBox c half1 ⊆ pureWZ2SourceBox newCenter half2 := by
    intro x hx
    have h1 : x ∈ wz1AxisBox c half1 := hx.1
    have h2 : x ∈ pureWZ2SourceWindow := hx.2
    have h3 : x ∈ wz1AxisBox c' half2 := hbox1_subset_box2 h1
    have h4 : x ∈ wz1AxisBox c' half2 ∩ pureWZ2SourceWindow := ⟨h3, h2⟩
    have h5 : x ∈ wz1AxisBox newCenter half2 := hbox2_cover h4
    exact ⟨h5, h2⟩
  have h_mass_transfer :
      ∑ i, MeasureTheory.volume (Y.carrier i ∩ pureWZ2SourceBox c half1) ≤
      ∑ i, MeasureTheory.volume (Y.carrier i ∩ pureWZ2SourceBox newCenter half2) := by
    apply Finset.sum_le_sum
    intro i _
    have h5 : Y.carrier i ∩ pureWZ2SourceBox c half1 ⊆ Y.carrier i ∩ pureWZ2SourceBox newCenter half2 := by
      intro x hx
      exact ⟨hx.1, h_full_inclusion hx.2⟩
    exact MeasureTheory.measure_mono h5
  have hmass' : ENNReal.ofReal (h ^ 3 / 125) * Y.mass ≤
      ∑ i, MeasureTheory.volume (Y.carrier i ∩ pureWZ2SourceBox newCenter half2) :=
    hmass.trans h_mass_transfer
  have h_eq : h ^ 3 / 125 = (((K : ℝ) - 1) * delta) ^ 3 / 125 := by
    simp [hh_def]
  rw [h_eq] at hmass'
  exact ⟨newCenter, hnewCenter_grid, hnewCenter_window, hmass'⟩

end Kakeya.Assouad

end
