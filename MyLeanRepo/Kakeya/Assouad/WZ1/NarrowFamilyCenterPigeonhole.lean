import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowDotSpreadExponentBound
import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowDotSpreadPointPigeonhole
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition8_9NarrowSplitStatements

/-!
# Generic center pigeonhole for narrow actual-edge families
-/

namespace Kakeya.Assouad

open scoped ENNReal

noncomputable def wz1NarrowFamilyCenterSpreadCardinality
    (delta epsilon eta workingLambda : ℝ) : ℝ :=
  Real.rpow delta
      (eta + workingLambda - 9 * epsilon / 10) /
    147456

noncomputable def wz1NarrowFamilyCenterConcentrationThreshold
    {α : Type*} [DecidableEq α]
    (source : Finset α)
    (delta epsilon eta workingLambda : ℝ) : ℝ :=
  (source.card : ℝ) /
    (3 *
      wz1NarrowFamilyCenterSpreadCardinality
        delta epsilon eta workingLambda)

structure WZ1NarrowFamilyCenterConcentratedData
    {α : Type*} [DecidableEq α]
    (source : Finset α)
    (centerValue : α → ℝ)
    (delta epsilon eta workingLambda : ℝ) where
  center : ℝ
  points : Finset α
  points_subset : points ⊆ source
  cardinality :
    wz1NarrowFamilyCenterConcentrationThreshold
        source delta epsilon eta workingLambda ≤
      (points.card : ℝ)
  concentrated :
    ∀ point ∈ points,
      |centerValue point - center| ≤ 3 * delta

theorem wz1_narrow_family_center_pigeonhole
    {α : Type*} [DecidableEq α]
    {delta epsilon eta workingLambda width : ℝ}
    {H : Finset (Point2 × Point2 × Point2)}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hepsilon : 0 < epsilon)
    (hepsilonOne : epsilon < 1)
    (heta : 0 < eta)
    (hworkingLambda : workingLambda ≤ epsilon / 100)
    (hetaSmall : eta ≤ epsilon / 20)
    (hdeltaWidth : delta ≤ width)
    (hnarrow :
      width ≤ Real.rpow delta (1 - epsilon / 10))
    (hsmall :
      (1200000 : ℝ) *
          Real.rpow delta (7 * epsilon / 10) ≤ 1)
    (source : Finset α)
    (hsource : source.Nonempty)
    (centerValue actualValue : α → ℝ)
    (hactualCenter :
      ∀ point ∈ source,
        |actualValue point - centerValue point| ≤ delta)
    (hactualRange :
      ∀ point ∈ source,
        -4 * width ≤ actualValue point ∧
          actualValue point ≤ 4 * width)
    (hactualDot :
      ∀ point ∈ source,
        actualValue point ∈ wz1DotDifferenceSet H) :
    Nonempty
        (WZ1Proposition8_9NarrowDotSpreadData
          delta epsilon eta H) ∨
      Nonempty
        (WZ1NarrowFamilyCenterConcentratedData
          source centerValue delta epsilon eta workingLambda) := by
  classical
  have hcenterRange :
      ∀ point ∈ source,
        -5 * width ≤ centerValue point ∧
          centerValue point ≤ 5 * width := by
    intro point hpoint
    have hcenter := hactualCenter point hpoint
    have hactual := hactualRange point hpoint
    have hlower :
        centerValue point ≥ actualValue point - delta := by
      have := (abs_le.mp hcenter).2
      linarith
    have hupper :
        centerValue point ≤ actualValue point + delta := by
      have := (abs_le.mp hcenter).1
      linarith
    constructor <;> linarith
  let target :=
    wz1NarrowFamilyCenterSpreadCardinality
      delta epsilon eta workingLambda
  have htarget : 0 < target := by
    dsimp only [target,
      wz1NarrowFamilyCenterSpreadCardinality]
    exact div_pos (Real.rpow_pos_of_pos hdelta _) (by norm_num)
  let threshold :=
    wz1NarrowFamilyCenterConcentrationThreshold
      source delta epsilon eta workingLambda
  have hsourcePositive : 0 < (source.card : ℝ) := by
    exact_mod_cast hsource.card_pos
  have hthreshold : 0 < threshold := by
    dsimp only [threshold,
      wz1NarrowFamilyCenterConcentrationThreshold]
    exact div_pos hsourcePositive
      (mul_pos (by norm_num) htarget)
  rcases
      point_separated_or_concentrated
        (source := source) (value := centerValue)
        (delta := 3 * delta)
        (lower := -5 * width) (upper := 5 * width)
        (K := threshold)
        (by positivity) hcenterRange hthreshold hsource with
    hconcentrated | hspread
  · rcases hconcentrated with ⟨center, hcard⟩
    exact Or.inr
      ⟨{
        center := center
        points :=
          source.filter fun point =>
            |centerValue point - center| ≤ 3 * delta
        points_subset := Finset.filter_subset _ _
        cardinality := by
          simpa [threshold] using hcard
        concentrated := by
          intro point hpoint
          exact (Finset.mem_filter.mp hpoint).2
      }⟩
  · rcases hspread with
      ⟨selected, hselectedSource, hcenterSeparated,
        hselectedCard⟩
    have hselectedTarget :
        target ≤ (selected.card : ℝ) := by
      have heq :
          (source.card : ℝ) / (3 * threshold) = target := by
        rw [show
          threshold =
            (source.card : ℝ) / (3 * target) by
              rfl]
        field_simp [hsourcePositive.ne', htarget.ne']
      exact (by simpa [heq] using hselectedCard)
    let values := selected.image actualValue
    have hactualSeparated :
        ∀ first ∈ selected, ∀ second ∈ selected,
          first ≠ second →
            2 * delta <
              |actualValue first - actualValue second| := by
      intro first hfirst second hsecond hne
      have hcenters :=
        hcenterSeparated first hfirst second hsecond hne
      have hfirstError :=
        hactualCenter first (hselectedSource hfirst)
      have hsecondError :=
        hactualCenter second (hselectedSource hsecond)
      have htriangle :
          |centerValue first - centerValue second| ≤
            |centerValue first - actualValue first| +
              |actualValue first - actualValue second| +
                |actualValue second - centerValue second| := by
        have hid :
            centerValue first - centerValue second =
              (centerValue first - actualValue first) +
                (actualValue first - actualValue second) +
                  (actualValue second - centerValue second) := by
          ring
        rw [hid]
        exact abs_add_three _ _ _
      have hfirstError' :
          |centerValue first - actualValue first| ≤ delta := by
        simpa [abs_sub_comm] using hfirstError
      linarith
    have hinjective :
        Set.InjOn actualValue (selected : Set α) := by
      intro first hfirst second hsecond heq
      by_contra hne
      have hsep :=
        hactualSeparated first hfirst second hsecond hne
      rw [heq, sub_self, abs_zero] at hsep
      linarith
    have hvaluesCard : values.card = selected.card :=
      Finset.card_image_of_injOn hinjective
    have hvaluesDot :
        (values : Set ℝ) ⊆ wz1DotDifferenceSet H := by
      intro value hvalue
      rcases Finset.mem_image.mp hvalue with
        ⟨point, hpoint, rfl⟩
      exact hactualDot point (hselectedSource hpoint)
    have hvaluesNonempty : values.Nonempty :=
      Finset.Nonempty.image
        (by
          have hpositive :
              0 < (selected.card : ℝ) :=
            htarget.trans_le hselectedTarget
          exact Finset.card_pos.mp (by exact_mod_cast hpositive))
        actualValue
    let lower := values.min' hvaluesNonempty
    let upper := values.max' hvaluesNonempty
    have hlower : lower ∈ values := Finset.min'_mem _ _
    have hupper : upper ∈ values := Finset.max'_mem _ _
    have hbetween :
        ∀ value ∈ values, lower ≤ value ∧ value ≤ upper := by
      intro value hvalue
      exact
        ⟨Finset.min'_le values value hvalue,
          Finset.le_max' values value hvalue⟩
    have hrange : upper - lower ≤ 8 * width := by
      rcases Finset.mem_image.mp hlower with
        ⟨lowerPoint, hlowerPoint, hlowerEq⟩
      rcases Finset.mem_image.mp hupper with
        ⟨upperPoint, hupperPoint, hupperEq⟩
      have hlowerBound :=
        (hactualRange lowerPoint
          (hselectedSource hlowerPoint)).1
      have hupperBound :=
        (hactualRange upperPoint
          (hselectedSource hupperPoint)).2
      rw [← hlowerEq, ← hupperEq]
      linarith
    have hseparated :
        ∀ first ∈ values, ∀ second ∈ values,
          first ≠ second → 2 * delta < |first - second| := by
      intro first hfirst second hsecond hne
      rcases Finset.mem_image.mp hfirst with
        ⟨firstPoint, hfirstPoint, rfl⟩
      rcases Finset.mem_image.mp hsecond with
        ⟨secondPoint, hsecondPoint, rfl⟩
      apply hactualSeparated firstPoint hfirstPoint
        secondPoint hsecondPoint
      intro heq
      apply hne
      rw [heq]
    let diameter := upper - lower
    have hcard :=
      narrow_dot_spread_exponent_bound
        hdelta hdeltaOne hepsilon hepsilonOne heta
        hworkingLambda hetaSmall hnarrow hsmall
        (values.card : ℝ)
        (by
          rw [hvaluesCard]
          simpa [target,
            wz1NarrowFamilyCenterSpreadCardinality] using
              hselectedTarget)
        diameter
        (sub_nonneg.mpr (hbetween upper hupper).1)
        (by simpa [diameter] using hrange)
    have hbase :
        2 *
              max ((upper - lower) / 2)
                (Real.rpow delta (1 - eta) / 2) /
            delta =
          max diameter (Real.rpow delta (1 - eta)) / delta := by
      dsimp only [diameter]
      rw [show
        max ((upper - lower) / 2)
            (Real.rpow delta (1 - eta) / 2) =
          max (upper - lower)
              (Real.rpow delta (1 - eta)) / 2 by
        exact max_div_div_right (by norm_num)
          (upper - lower) (Real.rpow delta (1 - eta))]
      ring
    rw [← hbase] at hcard
    exact Or.inl
      ⟨⟨values, lower, upper, hlower, hupper,
        hseparated, hvaluesDot, hbetween,
        by simpa [ENNReal.ofReal_natCast] using hcard⟩⟩

end Kakeya.Assouad
