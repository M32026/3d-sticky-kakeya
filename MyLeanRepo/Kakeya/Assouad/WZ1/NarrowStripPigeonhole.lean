import MyLeanRepo.Kakeya.Assouad.WZ1.GridPigeonhole

/-!
# One-dimensional pigeonhole inside a strip

This module isolates the elementary pigeonhole step used in the narrow
common-strip branch of PDF Proposition 8.9.  A finite set whose scalar
coordinates lie in an interval is partitioned into consecutive cells of
length `delta`; one cell contains the average number of points.
-/

namespace Kakeya.Assouad

noncomputable section

open scoped ENNReal

attribute [local instance] Classical.propDecidable

/--
If the values of `coordinate` on `points` lie in `[lower, upper]`, then one
interval of radius `delta` contains at least the average number of points over
at most `(upper - lower) / delta + 2` cells.
-/
lemma finite_interval_pigeonhole
    {α : Type*} [DecidableEq α]
    {points : Finset α}
    {delta lower upper : ℝ}
    (hdelta : 0 < delta)
    (hlowerUpper : lower ≤ upper)
    (coordinate : α → ℝ)
    (hcoordinate :
      ∀ point ∈ points,
        lower ≤ coordinate point ∧ coordinate point ≤ upper) :
    ∃ level : ℝ,
      (points.card : ℝ) ≤
        ((upper - lower) / delta + 2) *
          ((points.filter fun point =>
            |coordinate point - level| ≤ delta).card : ℝ) := by
  let cellCount : ℕ := Nat.ceil ((upper - lower) / delta)
  let cells : Finset ℕ := Finset.range (cellCount + 1)
  let cellIndex : α → ℕ :=
    fun point => Nat.floor ((coordinate point - lower) / delta)
  have hquotientNonneg : 0 ≤ (upper - lower) / delta := by
    exact div_nonneg (sub_nonneg.mpr hlowerUpper) hdelta.le
  have hmaps :
      ∀ point ∈ points, cellIndex point ∈ cells := by
    intro point hpoint
    have hbounds := hcoordinate point hpoint
    have hpointQuotientNonneg :
        0 ≤ (coordinate point - lower) / delta := by
      exact div_nonneg (sub_nonneg.mpr hbounds.1) hdelta.le
    have hpointQuotientUpper :
        (coordinate point - lower) / delta ≤
          (upper - lower) / delta := by
      exact div_le_div_of_nonneg_right
        (sub_le_sub_right hbounds.2 lower) hdelta.le
    have hpointQuotientCeil :
        (coordinate point - lower) / delta ≤
          (cellCount : ℝ) := by
      exact hpointQuotientUpper.trans
        (by
          dsimp only [cellCount]
          exact Nat.le_ceil _)
    have hfloorUpper :
        (cellIndex point : ℝ) ≤ (cellCount : ℝ) := by
      have hfloor :
          (cellIndex point : ℝ) ≤
            (coordinate point - lower) / delta := by
        dsimp only [cellIndex]
        exact Nat.floor_le hpointQuotientNonneg
      exact hfloor.trans hpointQuotientCeil
    have hindexUpper : cellIndex point ≤ cellCount := by
      exact_mod_cast hfloorUpper
    simpa [cells] using Nat.lt_succ_of_le hindexUpper
  have hcellsNonempty : cells.Nonempty := by
    simpa [cells] using (Finset.nonempty_range_add_one : (Finset.range (cellCount + 1)).Nonempty)
  rcases finset_pigeonhole hmaps hcellsNonempty with
    ⟨cell, hcell, hpigeonhole⟩
  let level : ℝ := lower + (cell : ℝ) * delta
  have hfiberSubset :
      points.filter (fun point => cellIndex point = cell) ⊆
        points.filter (fun point =>
          |coordinate point - level| ≤ delta) := by
    intro point hpoint
    have hpointMem := (Finset.mem_filter.mp hpoint).1
    have hindex := (Finset.mem_filter.mp hpoint).2
    have hbounds := hcoordinate point hpointMem
    have hpointQuotientNonneg :
        0 ≤ (coordinate point - lower) / delta := by
      exact div_nonneg (sub_nonneg.mpr hbounds.1) hdelta.le
    have hcellLower :
        (cell : ℝ) ≤ (coordinate point - lower) / delta := by
      rw [← hindex]
      dsimp only [cellIndex]
      exact Nat.floor_le hpointQuotientNonneg
    have hcellUpper :
        (coordinate point - lower) / delta < (cell : ℝ) + 1 := by
      rw [← hindex]
      dsimp only [cellIndex]
      exact Nat.lt_floor_add_one _
    have hlevelLower : level ≤ coordinate point := by
      dsimp only [level]
      have hscaled :
          (cell : ℝ) * delta ≤ coordinate point - lower := by
        calc
          (cell : ℝ) * delta ≤
              ((coordinate point - lower) / delta) * delta := by
            gcongr
          _ = coordinate point - lower := by
            field_simp [hdelta.ne']
      linarith
    have hlevelUpper : coordinate point < level + delta := by
      dsimp only [level]
      have hscaled :
          coordinate point - lower <
            ((cell : ℝ) + 1) * delta := by
        calc
          coordinate point - lower =
              ((coordinate point - lower) / delta) * delta := by
            field_simp [hdelta.ne']
          _ < ((cell : ℝ) + 1) * delta := by
            gcongr
      linarith
    exact
      Finset.mem_filter.mpr
        ⟨hpointMem, (abs_le.mpr ⟨by linarith, by linarith⟩)⟩
  have hfiberCard :
      ((points.filter fun point =>
        cellIndex point = cell).card : ℝ) ≤
      ((points.filter fun point =>
        |coordinate point - level| ≤ delta).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hfiberSubset
  have hcellCountBound :
      (cells.card : ℝ) ≤ (upper - lower) / delta + 2 := by
    have hceil :
        (cellCount : ℝ) < (upper - lower) / delta + 1 := by
      dsimp only [cellCount]
      exact Nat.ceil_lt_add_one hquotientNonneg
    simp only [cells, Finset.card_range, Nat.cast_add, Nat.cast_one]
    linarith
  refine ⟨level, hpigeonhole.trans ?_⟩
  calc
    (cells.card : ℝ) *
          ((points.filter fun point =>
            cellIndex point = cell).card : ℝ)
        ≤ (cells.card : ℝ) *
          ((points.filter fun point =>
            |coordinate point - level| ≤ delta).card : ℝ) := by
          gcongr
    _ ≤ ((upper - lower) / delta + 2) *
          ((points.filter fun point =>
            |coordinate point - level| ≤ delta).card : ℝ) := by
          gcongr

/--
Division form of `finite_interval_pigeonhole`.
-/
lemma finite_interval_pigeonhole_lower_bound
    {α : Type*} [DecidableEq α]
    {points : Finset α}
    {delta lower upper : ℝ}
    (hdelta : 0 < delta)
    (hlowerUpper : lower ≤ upper)
    (coordinate : α → ℝ)
    (hcoordinate :
      ∀ point ∈ points,
        lower ≤ coordinate point ∧ coordinate point ≤ upper) :
    ∃ level : ℝ,
      (points.card : ℝ) * delta /
          (upper - lower + 2 * delta) ≤
        ((points.filter fun point =>
          |coordinate point - level| ≤ delta).card : ℝ) := by
  rcases
      finite_interval_pigeonhole
        hdelta hlowerUpper coordinate hcoordinate with
    ⟨level, hlevel⟩
  have hfactorPos :
      0 < (upper - lower) / delta + 2 := by
    have hnonneg :
        0 ≤ (upper - lower) / delta := by
      exact div_nonneg (sub_nonneg.mpr hlowerUpper) hdelta.le
    linarith
  have hdivided :
      (points.card : ℝ) /
          ((upper - lower) / delta + 2) ≤
        ((points.filter fun point =>
          |coordinate point - level| ≤ delta).card : ℝ) :=
    (div_le_iff₀ hfactorPos).2 (by simpa [mul_comm] using hlevel)
  refine ⟨level, ?_⟩
  convert hdivided using 1
  field_simp [hdelta.ne']
  <;> ring

/--
A finite planar set contained in a scalar strip of radius `width` has a
parallel `delta`-strip containing the corresponding average fraction.
-/
lemma strip_pigeonhole_lower_bound
    {points : DiscreteSet 2}
    {delta center width : ℝ}
    (hdelta : 0 < delta)
    (hwidth : 0 ≤ width)
    (coordinate : Point2 → ℝ)
    (hstrip :
      ∀ point ∈ points,
        |coordinate point - center| ≤ width) :
    ∃ level : ℝ,
      (points.card : ℝ) * delta /
          (2 * width + 2 * delta) ≤
        ((points.filter fun point =>
          |coordinate point - level| ≤ delta).card : ℝ) := by
  have hcoordinate :
      ∀ point ∈ points,
        center - width ≤ coordinate point ∧
          coordinate point ≤ center + width := by
    intro point hpoint
    have hbounds := abs_le.mp (hstrip point hpoint)
    constructor <;> linarith
  rcases
      finite_interval_pigeonhole_lower_bound
        hdelta (by linarith : center - width ≤ center + width)
        coordinate hcoordinate with
    ⟨level, hlevel⟩
  refine ⟨level, ?_⟩
  convert hlevel using 1 <;> ring

end

end Kakeya.Assouad
