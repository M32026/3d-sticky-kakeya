import MyLeanRepo.Kakeya.Assouad.WZ1.GridCellPartition
import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.TubeBaseAlignment
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Cell-level pruning for local fullness

Prune each carrier by keeping only grid cells where the carrier has at least
`threshold` volume.  This guarantees the local fullness property used by WZ1
Lemma 17.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

/-- The grid cell with index `c` at scale `tau / 2`. -/
def gridCell (tau : ℝ) (c : ℤ × ℤ × ℤ) : Set Point3 :=
  {q | rhoGridIndex (tau / 2) q = c}

/-- Measurability of grid cells. -/
lemma gridCell_measurable {tau : ℝ} (c : ℤ × ℤ × ℤ) :
    MeasurableSet (gridCell tau c) := by
  have h0 :
      Measurable
        (fun p : Point3 =>
          ⌊p 0 / gridSide (tau / 2)⌋) :=
    Measurable.floor (by fun_prop)
  have h1 :
      Measurable
        (fun p : Point3 =>
          ⌊p 1 / gridSide (tau / 2)⌋) :=
    Measurable.floor (by fun_prop)
  have h2 :
      Measurable
        (fun p : Point3 =>
          ⌊p 2 / gridSide (tau / 2)⌋) :=
    Measurable.floor (by fun_prop)
  have hindex :
      rhoGridIndex (tau / 2) =
        fun p =>
          (⌊p 0 / gridSide (tau / 2)⌋,
            ⌊p 1 / gridSide (tau / 2)⌋,
              ⌊p 2 / gridSide (tau / 2)⌋) := by
    funext p
    simp [rhoGridIndex, gridIndex]
  rw [gridCell, hindex]
  exact (h0.prod (h1.prod h2)) (MeasurableSet.singleton c)

/-- A grid cell at scale `tau / 2` has diameter at most `tau`. -/
lemma gridCell_diameter
    {tau : ℝ} (htau : 0 < tau)
    {c : ℤ × ℤ × ℤ} {p q : Point3}
    (hp : p ∈ gridCell tau c)
    (hq : q ∈ gridCell tau c) :
    dist p q ≤ tau := by
  have hscale : 0 < tau / 2 := by linarith
  have hindex :
      rhoGridIndex (tau / 2) q =
        rhoGridIndex (tau / 2) p := by
    simpa [gridCell] using hq.trans hp.symm
  have hdist :
      dist q p ≤ 2 * (tau / 2) :=
    grid_cell_diameter hscale hindex
  rw [dist_comm] at hdist
  linarith

/--
If a carrier has enough volume in the grid cell containing `p`, then it has
enough volume in the radius-`tau` ball centered at `p`.
-/
lemma grid_cell_fullness
    {tau threshold : ℝ} (htau : 0 < tau)
    {C : Set Point3} {p : Point3} {c : ℤ × ℤ × ℤ}
    (hp : p ∈ gridCell tau c)
    (hvolume :
      ENNReal.ofReal threshold ≤
        volume (C ∩ gridCell tau c)) :
    ENNReal.ofReal threshold ≤
      volume (C ∩ Metric.closedBall p tau) := by
  apply hvolume.trans
  apply measure_mono
  rintro point ⟨hpointC, hpointCell⟩
  refine ⟨hpointC, ?_⟩
  rw [Metric.mem_closedBall]
  exact gridCell_diameter htau hpointCell hp

/--
Prune a shading by retaining exactly the grid cells whose carrier intersection
has at least `threshold` volume.
-/
def gridCellPrune
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (tau threshold : ℝ)
    (htau : 0 < tau) :
    Kakeya.Streamlined.TubeShading F :=
  let good (index : Fin F.card) (cell : ℤ × ℤ × ℤ) : Prop :=
    ENNReal.ofReal threshold ≤
      volume (Y.carrier index ∩ gridCell tau cell)
  { carrier := fun index =>
      {point |
        ∃ cell : ℤ × ℤ × ℤ,
          good index cell ∧
            point ∈ Y.carrier index ∩ gridCell tau cell}
    measurable_carrier := by
      intro index
      have heq :
          {point : Point3 |
              ∃ cell : ℤ × ℤ × ℤ,
                good index cell ∧
                  point ∈
                    Y.carrier index ∩ gridCell tau cell} =
            ⋃ cell : ℤ × ℤ × ℤ,
              if good index cell then
                Y.carrier index ∩ gridCell tau cell
              else ∅ := by
        ext point
        simp [good]
      rw [heq]
      apply MeasurableSet.iUnion
      intro cell
      by_cases hgood : good index cell
      · rw [if_pos hgood]
        exact (Y.measurable_carrier index).inter
          (gridCell_measurable cell)
      · rw [if_neg hgood]
        exact MeasurableSet.empty
    subset_body := by
      intro index point hpoint
      rcases hpoint with ⟨cell, _, hpointCarrier, _⟩
      exact Y.subset_body index hpointCarrier }

/-- Grid-cell pruning is a subshading. -/
lemma gridCellPrune_subshading
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {tau threshold : ℝ}
    {htau : 0 < tau} :
    IsSubshading (gridCellPrune Y tau threshold htau) Y := by
  intro index point hpoint
  rcases hpoint with ⟨cell, _, hpointCarrier, _⟩
  exact hpointCarrier

/-- Every retained point has the prescribed mass in its radius-`tau` ball. -/
lemma gridCellPrune_fullness
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {tau threshold : ℝ}
    (htau : 0 < tau)
    (_hthreshold : 0 ≤ threshold)
    {index : Fin F.card} {point : Point3}
    (hpoint :
      point ∈
        (gridCellPrune Y tau threshold htau).carrier index) :
    ENNReal.ofReal threshold ≤
      volume
        ((gridCellPrune Y tau threshold htau).carrier index ∩
          Metric.closedBall point tau) := by
  rcases hpoint with
    ⟨cell, hgood, hpointCarrier, hpointCell⟩
  have heq :
      (gridCellPrune Y tau threshold htau).carrier index ∩
          gridCell tau cell =
        Y.carrier index ∩ gridCell tau cell := by
    ext other
    constructor
    · rintro ⟨⟨_, _, hotherCarrier, _⟩, hotherCell⟩
      exact ⟨hotherCarrier, hotherCell⟩
    · rintro ⟨hotherCarrier, hotherCell⟩
      exact
        ⟨⟨cell, hgood, hotherCarrier, hotherCell⟩,
          hotherCell⟩
  apply
    grid_cell_fullness htau hpointCell
  rw [heq]
  exact hgood

/-- Grid cells intersecting a set. -/
def gridCellsIntersecting
    (tau : ℝ) (source : Set Point3) :
    Set (ℤ × ℤ × ℤ) :=
  {cell | (gridCell tau cell ∩ source).Nonempty}

/-- A ball of radius at most `3 * tau` meets at most `13^3` cells. -/
lemma gridCellsIntersecting_ball_bound
    {tau : ℝ} (htau : 0 < tau)
    (center : Point3) {radius : ℝ}
    (hradius : radius ≤ 3 * tau) :
    (gridCellsIntersecting tau
        (Metric.closedBall center radius)).Finite ∧
      Set.ncard
          (gridCellsIntersecting tau
            (Metric.closedBall center radius)) ≤
        13 ^ 3 := by
  have hscale : 0 < tau / 2 := by linarith
  let centerIndex := rhoGridIndex (tau / 2) center
  let first : Finset ℤ :=
    Finset.Icc (centerIndex.1 - 6) (centerIndex.1 + 6)
  let second : Finset ℤ :=
    Finset.Icc (centerIndex.2.1 - 6) (centerIndex.2.1 + 6)
  let third : Finset ℤ :=
    Finset.Icc (centerIndex.2.2 - 6) (centerIndex.2.2 + 6)
  let cells : Finset (ℤ × ℤ × ℤ) :=
    first ×ˢ (second ×ˢ third)
  have hfirst : first.card = 13 := by
    simp [first, Finset.Icc_eq_empty_of_lt] <;> norm_num <;> omega
  have hsecond : second.card = 13 := by
    simp [second, Finset.Icc_eq_empty_of_lt] <;> norm_num <;> omega
  have hthird : third.card = 13 := by
    simp [third, Finset.Icc_eq_empty_of_lt] <;> norm_num <;> omega
  have hcellsCard : cells.card = 13 ^ 3 := by
    rw [Finset.card_product, Finset.card_product,
      hfirst, hsecond, hthird]
    norm_num
  have hsubset :
      gridCellsIntersecting tau
          (Metric.closedBall center radius) ⊆
        (cells : Set (ℤ × ℤ × ℤ)) := by
    intro cell hcell
    rcases hcell with
      ⟨point, hpointCell, hpointBall⟩
    have hdist : dist point center ≤ radius :=
      Metric.mem_closedBall.mp hpointBall
    have hdist' : dist point center ≤ 6 * (tau / 2) := by
      linarith
    have hpointIndex :
        rhoGridIndex (tau / 2) point = cell := by
      simpa [gridCell] using hpointCell
    have hneighbors :=
      grid_neighbor_count hscale hdist'
    have hcoordinate :
        |cell.1 - centerIndex.1| ≤ 6 ∧
          |cell.2.1 - centerIndex.2.1| ≤ 6 ∧
            |cell.2.2 - centerIndex.2.2| ≤ 6 := by
      simpa [centerIndex, hpointIndex] using hneighbors
    have hfirstMem : cell.1 ∈ first := by
      simp only [first, Finset.mem_Icc]
      constructor <;>
        linarith [abs_le.mp hcoordinate.1]
    have hsecondMem : cell.2.1 ∈ second := by
      simp only [second, Finset.mem_Icc]
      constructor <;>
        linarith [abs_le.mp hcoordinate.2.1]
    have hthirdMem : cell.2.2 ∈ third := by
      simp only [third, Finset.mem_Icc]
      constructor <;>
        linarith [abs_le.mp hcoordinate.2.2]
    exact Finset.mem_product.mpr
      ⟨hfirstMem,
        Finset.mem_product.mpr ⟨hsecondMem, hthirdMem⟩⟩
  have hfinite :
      (gridCellsIntersecting tau
        (Metric.closedBall center radius)).Finite :=
    cells.finite_toSet.subset hsubset
  have hncard :
      Set.ncard
          (gridCellsIntersecting tau
            (Metric.closedBall center radius)) ≤
        Set.ncard (cells : Set (ℤ × ℤ × ℤ)) :=
    Set.ncard_le_ncard hsubset cells.finite_toSet
  have hcoe :
      Set.ncard (cells : Set (ℤ × ℤ × ℤ)) =
        cells.card := by
    simp
  rw [hcoe, hcellsCard] at hncard
  exact ⟨hfinite, hncard⟩

/--
A radius-`rho` unit tube with `rho ≤ tau` meets at most
`(ceil (1 / tau) + 1) * 13^3` cells.
-/
lemma gridCellsIntersecting_tube_bound
    {tau rho : ℝ}
    (htau : 0 < tau)
    (hrho : 0 < rho)
    (hrho_tau : rho ≤ tau)
    (tube : Kakeya.DeltaTube rho)
    (htau_one : tau ≤ 1) :
    (gridCellsIntersecting tau tube.carrier).Finite ∧
      Set.ncard (gridCellsIntersecting tau tube.carrier) ≤
        (Nat.ceil (1 / tau) + 1) * 13 ^ 3 := by
  let count := Nat.ceil (1 / tau)
  let center : ℕ → Point3 := fun index =>
    tube.base + ((index : ℝ) * tau) • tube.direction
  have hcover :
      tube.carrier ⊆
        ⋃ index ∈ Finset.range (count + 1),
          Metric.closedBall (center index) (2 * tau) := by
    intro point hpoint
    rcases tube_carrier_decomp hrho.le tube point hpoint with
      ⟨parameter, hparameter, error, herror, rfl⟩
    have hratio : 0 ≤ parameter / tau :=
      div_nonneg hparameter.1 htau.le
    let index := Nat.floor (parameter / tau)
    have hindexCount : index ≤ count := by
      have hparameterRatio :
          parameter / tau ≤ 1 / tau := by
        gcongr
        exact hparameter.2
      have hindexRatio :
          (index : ℝ) ≤ parameter / tau :=
        Nat.floor_le hratio
      have hcountRatio :
          1 / tau ≤ (count : ℝ) :=
        Nat.le_ceil (1 / tau)
      exact_mod_cast hindexRatio.trans
        (hparameterRatio.trans hcountRatio)
    have hindexRange :
        index ∈ Finset.range (count + 1) := by
      simp only [Finset.mem_range]
      omega
    have hindexLower :
        (index : ℝ) * tau ≤ parameter := by
      have h :=
        mul_le_mul_of_nonneg_right
          (Nat.floor_le hratio) htau.le
      simpa [div_mul_eq_mul_div, htau.ne'] using h
    have hindexUpper :
        parameter < ((index : ℝ) + 1) * tau := by
      have h :=
        mul_lt_mul_of_pos_right
          (Nat.lt_floor_add_one (parameter / tau)) htau
      calc
        parameter = (parameter / tau) * tau := by
          field_simp [htau.ne']
        _ < ((index : ℝ) + 1) * tau := h
    have hparameterClose :
        |parameter - (index : ℝ) * tau| ≤ tau := by
      rw [abs_le]
      constructor <;> linarith
    have hdist :
        ‖(parameter - (index : ℝ) * tau) • tube.direction +
              error‖ ≤
          2 * tau := by
      calc
        ‖(parameter - (index : ℝ) * tau) • tube.direction +
              error‖
            ≤
          ‖(parameter - (index : ℝ) * tau) • tube.direction‖ +
            ‖error‖ := norm_add_le _ _
        _ =
            |parameter - (index : ℝ) * tau| +
              ‖error‖ := by
          rw [norm_smul, tube.direction_unit, mul_one,
            Real.norm_eq_abs]
        _ ≤ tau + rho := by
          gcongr
        _ ≤ 2 * tau := by linarith
    have hdifference :
        tube.base + parameter • tube.direction + error -
            center index =
          (parameter - (index : ℝ) * tau) • tube.direction +
            error := by
      simp [center, sub_smul]
      abel
    have hball :
        tube.base + parameter • tube.direction + error ∈
          Metric.closedBall (center index) (2 * tau) := by
      rw [Metric.mem_closedBall, dist_eq_norm, hdifference]
      exact hdist
    exact Set.mem_iUnion₂.mpr
      ⟨index, hindexRange, hball⟩
  have hsubset :
      gridCellsIntersecting tau tube.carrier ⊆
        ⋃ index ∈ Finset.range (count + 1),
          gridCellsIntersecting tau
            (Metric.closedBall (center index) (2 * tau)) := by
    intro cell hcell
    rcases hcell with
      ⟨point, hpointCell, hpointTube⟩
    rcases Set.mem_iUnion₂.mp (hcover hpointTube) with
      ⟨index, hindex, hpointBall⟩
    exact Set.mem_iUnion₂.mpr
      ⟨index, hindex,
        ⟨point, hpointCell, hpointBall⟩⟩
  have hfinitePiece :
      ∀ index ∈ Finset.range (count + 1),
        (gridCellsIntersecting tau
          (Metric.closedBall (center index) (2 * tau))).Finite := by
    intro index _
    exact
      (gridCellsIntersecting_ball_bound htau
        (center index) (by linarith)).1
  have hfiniteUnion :
      (⋃ index ∈ Finset.range (count + 1),
        gridCellsIntersecting tau
          (Metric.closedBall (center index) (2 * tau))).Finite :=
    Set.Finite.biUnion
      (Finset.range (count + 1)).finite_toSet hfinitePiece
  have hfinite :
      (gridCellsIntersecting tau tube.carrier).Finite :=
    hfiniteUnion.subset hsubset
  have hncard :
      Set.ncard (gridCellsIntersecting tau tube.carrier) ≤
        Set.ncard
          (⋃ index ∈ Finset.range (count + 1),
            gridCellsIntersecting tau
              (Metric.closedBall (center index) (2 * tau))) :=
    Set.ncard_le_ncard hsubset hfiniteUnion
  have hunionCard :
      Set.ncard
          (⋃ index ∈ Finset.range (count + 1),
            gridCellsIntersecting tau
              (Metric.closedBall (center index) (2 * tau))) ≤
        ∑ index ∈ Finset.range (count + 1),
          Set.ncard
            (gridCellsIntersecting tau
              (Metric.closedBall (center index) (2 * tau))) := by
    induction Finset.range (count + 1) using Finset.induction with
    | empty => simp
    | @insert index indices hindex ih =>
        rw [Finset.sum_insert hindex]
        have hiUnion :
            (⋃ value ∈ insert index indices,
                gridCellsIntersecting tau
                  (Metric.closedBall
                    (center value) (2 * tau))) =
              gridCellsIntersecting tau
                  (Metric.closedBall (center index) (2 * tau)) ∪
                ⋃ value ∈ indices,
                  gridCellsIntersecting tau
                    (Metric.closedBall
                      (center value) (2 * tau)) := by
          ext cell
          simp [Finset.mem_insert]
        rw [hiUnion]
        exact (Set.ncard_union_le _ _).trans
          (Nat.add_le_add_left ih _)
  have hsum :
      ∑ index ∈ Finset.range (count + 1),
          Set.ncard
            (gridCellsIntersecting tau
              (Metric.closedBall (center index) (2 * tau))) ≤
        (count + 1) * 13 ^ 3 := by
    calc
      ∑ index ∈ Finset.range (count + 1),
            Set.ncard
              (gridCellsIntersecting tau
                (Metric.closedBall (center index) (2 * tau)))
          ≤
        ∑ _index ∈ Finset.range (count + 1), 13 ^ 3 :=
          Finset.sum_le_sum fun index _ =>
            (gridCellsIntersecting_ball_bound htau
              (center index) (by linarith)).2
      _ = (count + 1) * 13 ^ 3 := by
        simp [Finset.sum_const]
  exact ⟨hfinite, hncard.trans (hunionCard.trans hsum)⟩

/--
The volume removed from one carrier is at most the number of intersecting
cells times the pruning threshold.
-/
lemma gridCellPrune_carrier_loss
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {tau threshold : ℝ}
    (htau : 0 < tau)
    (_hthreshold : 0 ≤ threshold)
    (hdelta : 0 < delta)
    (hdelta_tau : delta ≤ tau)
    (htau_one : tau ≤ 1)
    (index : Fin F.card)
    {bound : ℕ}
    (hbound :
      Set.ncard
          (gridCellsIntersecting tau (Y.carrier index)) ≤
        bound) :
    volume
        (Y.carrier index \
          (gridCellPrune Y tau threshold htau).carrier index) ≤
      (bound : ENNReal) * ENNReal.ofReal threshold := by
  let source := Y.carrier index
  let cellSet := gridCellsIntersecting tau source
  have hcellSetFinite : cellSet.Finite := by
    have hsubset :
        cellSet ⊆
          gridCellsIntersecting tau (F.tube index).carrier := by
      intro cell hcell
      rcases hcell with
        ⟨point, hpointCell, hpointSource⟩
      exact
        ⟨point, hpointCell,
          Y.subset_body index hpointSource⟩
    exact
      (gridCellsIntersecting_tube_bound htau hdelta
        hdelta_tau (F.tube index) htau_one).1.subset hsubset
  let cells : Finset (ℤ × ℤ × ℤ) :=
    hcellSetFinite.toFinset
  have hcellsCoe :
      (cells : Set (ℤ × ℤ × ℤ)) = cellSet :=
    Set.Finite.coe_toFinset hcellSetFinite
  let good (cell : ℤ × ℤ × ℤ) : Prop :=
    ENNReal.ofReal threshold ≤
      volume (source ∩ gridCell tau cell)
  let badCells : Finset (ℤ × ℤ × ℤ) :=
    cells.filter fun cell => ¬ good cell
  have hremoved :
      source \
          (gridCellPrune Y tau threshold htau).carrier index ⊆
        ⋃ cell ∈ badCells,
          source ∩ gridCell tau cell := by
    intro point hpoint
    let cell := rhoGridIndex (tau / 2) point
    have hpointCell : point ∈ gridCell tau cell := rfl
    have hcell : cell ∈ cells := by
      have : cell ∈ cellSet :=
        ⟨point, hpointCell, hpoint.1⟩
      rw [← hcellsCoe] at this
      simpa using this
    have hbad : ¬ good cell := by
      intro hgood
      exact hpoint.2
        ⟨cell, hgood, hpoint.1, hpointCell⟩
    exact Set.mem_iUnion₂.mpr
      ⟨cell,
        Finset.mem_filter.mpr ⟨hcell, hbad⟩,
        hpoint.1, hpointCell⟩
  have hvolume :
      volume
          (source \
            (gridCellPrune Y tau threshold htau).carrier index) ≤
        ∑ cell ∈ badCells,
          volume (source ∩ gridCell tau cell) := by
    exact
      (measure_mono hremoved).trans
        (measure_biUnion_finset_le badCells
          fun cell => source ∩ gridCell tau cell)
  have hbadVolume :
      ∀ cell ∈ badCells,
        volume (source ∩ gridCell tau cell) ≤
          ENNReal.ofReal threshold := by
    intro cell hcell
    exact le_of_not_ge (Finset.mem_filter.mp hcell).2
  have hsum :
      ∑ cell ∈ badCells,
          volume (source ∩ gridCell tau cell) ≤
        (badCells.card : ENNReal) *
          ENNReal.ofReal threshold := by
    calc
      ∑ cell ∈ badCells,
            volume (source ∩ gridCell tau cell)
          ≤
        ∑ _cell ∈ badCells,
          ENNReal.ofReal threshold :=
            Finset.sum_le_sum hbadVolume
      _ =
          (badCells.card : ENNReal) *
            ENNReal.ofReal threshold := by
        simp [Finset.sum_const]
  have hbadCard : badCells.card ≤ cells.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hcellsCard :
      (cells.card : ENNReal) =
        Set.ncard cellSet := by
    have :
        Set.ncard (cells : Set (ℤ × ℤ × ℤ)) =
          cells.card := by simp
    rw [hcellsCoe] at this
    exact_mod_cast this.symm
  have hfinal :
      (badCells.card : ENNReal) ≤ (bound : ENNReal) := by
    calc
      (badCells.card : ENNReal)
          ≤ (cells.card : ENNReal) := by
        exact_mod_cast hbadCard
      _ = Set.ncard cellSet := hcellsCard
      _ ≤ (bound : ENNReal) := by
        exact_mod_cast hbound
  exact hvolume.trans <| hsum.trans <| by
    gcongr

end Kakeya.Assouad
