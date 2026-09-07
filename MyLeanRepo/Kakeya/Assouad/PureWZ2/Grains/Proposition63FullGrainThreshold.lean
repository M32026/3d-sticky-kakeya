import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.GoodLine
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma18SpatialSelfCenteredCover
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma18CellNormalProjectionTransfer
import MyLeanRepo.Kakeya.Assouad.WZ1.IntervalADHelpers
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Full-grain thresholding for Proposition 6.3

This file contains the measure-theoretic deletion step in the paper's
Lemma 4.11.  A finite cover of a scalar projection partitions a measurable
set into projection grains.  Discarding grains below the average threshold
keeps half of the prescribed volume, and every remaining point is centered
in a slab carrying the same uniform volume floor.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset Metric

attribute [local instance] Classical.propDecidable

/-- Replace a finite radius-`rho` cover of a real set by a radius-`rho / 2`
cover with at most twice as many centers. -/
lemma proposition63_half_radius_cover
    {set : Set ℝ} {rho : ℝ} (hrho : 0 < rho)
    (centers : Finset ℝ)
    (hcover : set ⊆ ⋃ center ∈ centers, Metric.closedBall center rho) :
    ∃ refined : Finset ℝ,
      refined.card ≤ 2 * centers.card ∧
      set ⊆ ⋃ center ∈ refined, Metric.closedBall center (rho / 2) := by
  let refined : Finset ℝ := centers.biUnion fun center =>
    {center - rho / 2, center + rho / 2}
  have hcard : refined.card ≤ 2 * centers.card := by
    calc
      refined.card ≤ ∑ center ∈ centers,
          ({center - rho / 2, center + rho / 2} : Finset ℝ).card :=
        Finset.card_biUnion_le
      _ = ∑ _center ∈ centers, 2 := by
        apply Finset.sum_congr rfl
        intro center _
        rw [Finset.card_pair]
        linarith
      _ = 2 * centers.card := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  refine ⟨refined, hcard, ?_⟩
  intro value hvalue
  rcases Set.mem_iUnion₂.mp (hcover hvalue) with
    ⟨center, hcenter, hball⟩
  have hdistance : |value - center| ≤ rho := by
    simpa [Real.dist_eq] using hball
  by_cases hleft : value ≤ center
  · have hnew : |value - (center - rho / 2)| ≤ rho / 2 := by
      rw [abs_le]
      constructor <;> linarith [abs_le.mp hdistance]
    have hmem : center - rho / 2 ∈ refined :=
      Finset.mem_biUnion.mpr ⟨center, hcenter, by simp⟩
    exact Set.mem_iUnion₂.mpr
      ⟨center - rho / 2, hmem, Metric.mem_closedBall.mpr <| by
        rw [Real.dist_eq]
        convert hnew using 1 <;> ring⟩
  · have hright : center < value := lt_of_not_ge hleft
    have hnew : |value - (center + rho / 2)| ≤ rho / 2 := by
      rw [abs_le]
      constructor <;> linarith [abs_le.mp hdistance]
    have hmem : center + rho / 2 ∈ refined :=
      Finset.mem_biUnion.mpr ⟨center, hcenter, by simp⟩
    exact Set.mem_iUnion₂.mpr
      ⟨center + rho / 2, hmem, by simpa [Real.dist_eq] using hnew⟩

/-- Realize a finite external cover whose cardinality is bounded by any
finite ENNReal upper bound for `externalCoveringNumber`. -/
lemma proposition63_externalCoveringNumber_finite_cover
    {set : Set ℝ} {rho : ℝ} (hrho : 0 < rho)
    {bound : ENNReal} (hboundFinite : bound ≠ ⊤)
    (hbound :
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho) set) :
          ENNReal) ≤ bound) :
    ∃ centers : Finset ℝ,
      (centers.card : ENNReal) ≤ bound ∧
      set ⊆ ⋃ center ∈ centers, Metric.closedBall center rho := by
  let radius : NNReal := Real.toNNReal rho
  have hnumberFinite : Metric.externalCoveringNumber radius set ≠ ⊤ := by
    have hlt :
        (↑(Metric.externalCoveringNumber radius set) : ENNReal) < ⊤ :=
      hbound.trans_lt (lt_top_iff_ne_top.mpr hboundFinite)
    exact_mod_cast hlt.ne
  let Cover := {candidate : Set ℝ // Metric.IsCover radius set candidate}
  have finiteCoverExists : ∃ candidate : Set ℝ,
      Metric.IsCover radius set candidate ∧ candidate.Finite := by
    simpa [Metric.externalCoveringNumber, iInf_eq_top,
      Set.encard_eq_top_iff] using hnumberFinite
  have coverNonempty : Nonempty Cover := by
    rcases finiteCoverExists with ⟨candidate, hcandidate, _⟩
    exact ⟨⟨candidate, hcandidate⟩⟩
  let cardinality : Cover → ENat := fun candidate =>
    (candidate : Set ℝ).encard
  have hinf : (⨅ candidate : Cover, cardinality candidate) =
      Metric.externalCoveringNumber radius set := by
    simp only [cardinality, Cover, Metric.externalCoveringNumber,
      iInf_subtype, iInf_and]
  rcases ENat.exists_eq_iInf cardinality with ⟨minimal, hminimal⟩
  have hminimalEq : minimal.val.encard =
      Metric.externalCoveringNumber radius set := by
    rw [← hinf]
    exact hminimal
  have hminimalFinite : minimal.val.Finite := by
    apply Set.encard_lt_top_iff.mp
    rw [hminimalEq]
    exact lt_top_iff_ne_top.mpr hnumberFinite
  let centers : Finset ℝ := hminimalFinite.toFinset
  have hcentersSet : (centers : Set ℝ) = minimal.val :=
    hminimalFinite.coe_toFinset
  have hcover : set ⊆
      ⋃ center ∈ centers, Metric.closedBall center rho := by
    have hminimalCover : Metric.IsCover radius set (centers : Set ℝ) := by
      rw [hcentersSet]
      exact minimal.property
    have hraw := Metric.IsCover.subset_iUnion_closedBall hminimalCover
    simpa [radius, Real.toNNReal_of_nonneg hrho.le] using hraw
  have hcardENat : (centers.card : ENat) = minimal.val.encard := by
    simpa [centers] using
      hminimalFinite.encard_eq_coe_toFinset_card.symm
  have hcard : (centers.card : ENNReal) ≤ bound := by
    calc
      (centers.card : ENNReal) =
          (minimal.val.encard : ENNReal) := by exact_mod_cast hcardENat
      _ = (↑(Metric.externalCoveringNumber radius set) : ENNReal) := by
        exact_mod_cast hminimalEq
      _ ≤ bound := hbound
  exact ⟨centers, hcard, hcover⟩

/-- Threshold a finite family of projection grains.  At most half of the
prescribed volume lies in sub-threshold grains, so the remaining measurable
set retains the other half and has a uniform centered slab floor. -/
lemma proposition63_fullGrainThreshold_of_finiteCover
    {E : Set Point3} (hE : MeasurableSet E)
    (hEFinite : volume E ≠ ⊤)
    (normal : Point3)
    {rho : ℝ} (hrho : 0 < rho)
    (coverBudget : ℕ) (hcoverBudgetPos : 0 < coverBudget)
    (centers : Finset ℝ)
    (hcenters : centers.card ≤ 2 * coverBudget)
    (hcover : (fun point : Point3 => inner ℝ point normal) '' E ⊆
      ⋃ center ∈ centers, Metric.closedBall center (rho / 2))
    (retainedVolume threshold : ENNReal)
    (hretainedFinite : retainedVolume ≠ ⊤)
    (htwice : 2 * retainedVolume ≤ volume E)
    (hthreshold : threshold =
      retainedVolume / (2 * (coverBudget : ENNReal))) :
    ∃ good : Set Point3,
      MeasurableSet good ∧
      good ⊆ E ∧
      retainedVolume ≤ volume good ∧
      ∀ point ∈ good,
        threshold ≤ volume
          (good ∩ {other |
            |inner ℝ other normal - inner ℝ point normal| ≤ rho}) := by
  let grain (center : ℝ) : Set Point3 :=
    E ∩ {point | inner ℝ point normal ∈
      Metric.closedBall center (rho / 2)}
  let goodCenters : Finset ℝ := centers.filter fun center =>
    threshold ≤ volume (grain center)
  let good : Set Point3 := ⋃ center ∈ goodCenters, grain center
  let badCenters : Finset ℝ := centers \ goodCenters
  let bad : Set Point3 := ⋃ center ∈ badCenters, grain center
  have hgrainMeasurable : ∀ center, MeasurableSet (grain center) := by
    intro center
    exact hE.inter <| Metric.isClosed_closedBall.measurableSet.preimage <| by
      fun_prop
  have hgoodMeasurable : MeasurableSet good :=
    measurableSet_biUnion goodCenters fun center _ =>
      hgrainMeasurable center
  have hgoodSub : good ⊆ E := by
    rintro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨center, _, hpointGrain⟩
    exact hpointGrain.1
  have hbadVolume : volume bad ≤ retainedVolume := by
    calc
      volume bad ≤ ∑ center ∈ badCenters, volume (grain center) :=
        measure_biUnion_finset_le badCenters grain
      _ ≤ ∑ _center ∈ badCenters, threshold := by
        apply Finset.sum_le_sum
        intro center hcenter
        exact le_of_lt <| not_le.mp <| by
          intro hgood
          exact (Finset.mem_sdiff.mp hcenter).2 <|
            Finset.mem_filter.mpr
              ⟨(Finset.mem_sdiff.mp hcenter).1, hgood⟩
      _ = (badCenters.card : ENNReal) * threshold := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * (coverBudget : ENNReal)) * threshold := by
        gcongr
        exact_mod_cast
          (Finset.card_le_card (Finset.sdiff_subset)).trans hcenters
      _ = retainedVolume := by
        rw [hthreshold]
        apply ENNReal.mul_div_cancel
        · exact mul_ne_zero (by norm_num) <| by exact_mod_cast hcoverBudgetPos.ne'
        · exact ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top
  have hcovered : E ⊆ good ∪ bad := by
    intro point hpoint
    have hprojection : inner ℝ point normal ∈
        (fun other : Point3 => inner ℝ other normal) '' E :=
      ⟨point, hpoint, rfl⟩
    rcases Set.mem_iUnion₂.mp (hcover hprojection) with
      ⟨center, hcenter, hpointBall⟩
    have hpointGrain : point ∈ grain center := ⟨hpoint, hpointBall⟩
    by_cases hgood : center ∈ goodCenters
    · exact Or.inl <| Set.mem_iUnion₂.mpr
        ⟨center, hgood, hpointGrain⟩
    · exact Or.inr <| Set.mem_iUnion₂.mpr
        ⟨center, Finset.mem_sdiff.mpr ⟨hcenter, hgood⟩, hpointGrain⟩
  have hgoodVolume : retainedVolume ≤ volume good := by
    by_contra hnot
    have hgoodLt : volume good < retainedVolume := lt_of_not_ge hnot
    have hsum : volume E ≤ volume good + volume bad :=
      (measure_mono hcovered).trans (measure_union_le good bad)
    have hsumLt : volume good + volume bad <
        retainedVolume + retainedVolume :=
      calc
        volume good + volume bad ≤ volume good + retainedVolume :=
          add_le_add_right hbadVolume (volume good)
        _ < retainedVolume + retainedVolume :=
          ENNReal.add_lt_add_right hretainedFinite hgoodLt
    have hdouble : retainedVolume + retainedVolume =
        2 * retainedVolume := by ring
    rw [hdouble] at hsumLt
    exact (not_lt_of_ge (htwice.trans hsum)) hsumLt
  have hslab : ∀ point ∈ good,
      threshold ≤ volume
        (good ∩ {other |
          |inner ℝ other normal - inner ℝ point normal| ≤ rho}) := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨center, hcenter, hpointGrain⟩
    have hgrainThreshold : threshold ≤ volume (grain center) :=
      (Finset.mem_filter.mp hcenter).2
    apply hgrainThreshold.trans
    apply measure_mono
    intro other hother
    refine ⟨Set.mem_iUnion₂.mpr ⟨center, hcenter, hother⟩, ?_⟩
    have hotherProjection :
        |inner ℝ other normal - center| ≤ rho / 2 := by
      simpa [Real.dist_eq] using hother.2
    have hpointProjection :
        |inner ℝ point normal - center| ≤ rho / 2 := by
      simpa [Real.dist_eq] using hpointGrain.2
    calc
      |inner ℝ other normal - inner ℝ point normal| =
          |(inner ℝ other normal - center) -
            (inner ℝ point normal - center)| := by ring
      _ ≤ |inner ℝ other normal - center| +
          |inner ℝ point normal - center| := abs_sub _ _
      _ ≤ rho / 2 + rho / 2 := by gcongr
      _ = rho := by ring
  exact ⟨good, hgoodMeasurable, hgoodSub, hgoodVolume, hslab⟩

/-- External-covering-number form of the full-grain thresholding lemma. -/
lemma proposition63_fullGrainThreshold
    {E : Set Point3} (hE : MeasurableSet E)
    (hEFinite : volume E ≠ ⊤)
    (normal : Point3)
    {rho : ℝ} (hrho : 0 < rho)
    (retainedVolume threshold : ENNReal)
    (hretainedFinite : retainedVolume ≠ ⊤)
    (htwice : 2 * retainedVolume ≤ volume E)
    (coverBound : ℕ) (hcoverBoundPos : 0 < coverBound)
    (hcovering :
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
        ((fun point : Point3 => inner ℝ point normal) '' E)) : ENNReal) ≤
        (coverBound : ENNReal))
    (hthreshold : threshold =
      retainedVolume / (2 * (coverBound : ENNReal))) :
    ∃ good : Set Point3,
      MeasurableSet good ∧
      good ⊆ E ∧
      retainedVolume ≤ volume good ∧
      ∀ point ∈ good,
        threshold ≤ volume
          (good ∩ {other |
            |inner ℝ other normal - inner ℝ point normal| ≤ rho}) := by
  rcases proposition63_externalCoveringNumber_finite_cover hrho
      (bound := (coverBound : ENNReal)) (by simp) hcovering with
    ⟨centers, hcentersCard, hcentersCover⟩
  rcases proposition63_half_radius_cover hrho centers hcentersCover with
    ⟨refined, hrefinedCard, hrefinedCover⟩
  have hcentersNat : centers.card ≤ coverBound := by
    exact_mod_cast hcentersCard
  have hrefinedBound : refined.card ≤ 2 * coverBound :=
    hrefinedCard.trans (Nat.mul_le_mul_left 2 hcentersNat)
  exact proposition63_fullGrainThreshold_of_finiteCover hE hEFinite normal
    hrho coverBound hcoverBoundPos refined hrefinedBound hrefinedCover
    retainedVolume threshold hretainedFinite htwice hthreshold

/-- The complete cellwise output of the thresholding/Fubini step.  The good
line is selected only after the low-volume projection grains have been
discarded, so every parameter actually met by that line carries the same
full-grain slab lower bound. -/
structure Proposition63FullGrainFubiniCellData
    (E : Set Point3) (normal : Point3) (rho diameter lineVolume : ℝ)
    (retainedVolume threshold : ENNReal) where
  good : Set Point3
  good_measurable : MeasurableSet good
  good_subset : good ⊆ E
  good_volume : retainedVolume ≤ volume good
  center : Point3
  good_ball : good ⊆ Metric.closedBall center diameter
  normal_unit : ‖normal‖ = 1
  anchor : Point3
  anchor_mem : anchor ∈ good
  line_volume :
    ENNReal.ofReal (lineVolume / (4 * diameter ^ 2)) ≤
      volume {t : ℝ | anchor + t • normal ∈ good}
  relative_line_volume :
    volume good ≤ ENNReal.ofReal (4 * diameter ^ 2) *
      volume {t : ℝ | anchor + t • normal ∈ good}
  full_grain :
    ∀ t : ℝ, anchor + t • normal ∈ good →
      threshold ≤ volume
        (good ∩ {point |
          |inner ℝ point normal -
            inner ℝ (anchor + t • normal) normal| ≤ rho})

/-- Combine projection-grain thresholding with directional Fubini inside one
cell.  All geometry is explicit: the original cell is enclosed by one ball
of radius `diameter`, and the selected line uses the same unit normal as the
full-grain slabs. -/
theorem proposition63_fullGrainFubiniCell
    {E : Set Point3} (hE : MeasurableSet E)
    (hEFinite : volume E ≠ ⊤)
    (normal : Point3) (hnormal : ‖normal‖ = 1)
    {rho diameter lineVolume : ℝ}
    (hrho : 0 < rho) (hdiameter : 0 < diameter)
    (center : Point3) (hEball : E ⊆ Metric.closedBall center diameter)
    (retainedVolume threshold : ENNReal)
    (hretainedFinite : retainedVolume ≠ ⊤)
    (htwice : 2 * retainedVolume ≤ volume E)
    (hlineVolume : 0 < lineVolume)
    (hlineFloor : ENNReal.ofReal lineVolume ≤ retainedVolume)
    (coverBound : ℕ) (hcoverBoundPos : 0 < coverBound)
    (hcovering :
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
        ((fun point : Point3 => inner ℝ point normal) '' E)) : ENNReal) ≤
        (coverBound : ENNReal))
    (hthreshold : threshold =
      retainedVolume / (2 * (coverBound : ENNReal))) :
    Nonempty (Proposition63FullGrainFubiniCellData E normal rho diameter
      lineVolume retainedVolume threshold) := by
  rcases proposition63_fullGrainThreshold hE hEFinite normal hrho
      retainedVolume threshold hretainedFinite htwice coverBound
      hcoverBoundPos hcovering hthreshold with
    ⟨good, hgoodMeasurable, hgoodSubset, hgoodVolume, hfullGrain⟩
  have hgoodFinite : volume good ≠ ⊤ :=
    ne_top_of_le_ne_top hEFinite (measure_mono hgoodSubset)
  have hgoodBall : good ⊆ Metric.closedBall center diameter :=
    hgoodSubset.trans hEball
  have hgoodPos : volume good ≠ 0 := by
    intro hgoodZero
    have hretainedZero : retainedVolume = 0 := by
      exact bot_unique (hgoodVolume.trans_eq hgoodZero)
    have hlineZero : ENNReal.ofReal lineVolume = 0 := by
      exact bot_unique (hlineFloor.trans_eq hretainedZero)
    exact (ENNReal.ofReal_pos.mpr hlineVolume).ne' hlineZero
  rcases fubini_directional_line_selection_relative hgoodMeasurable
      hgoodFinite hgoodPos hdiameter center hgoodBall normal hnormal with
    ⟨anchor, hanchor, hrelativeLine⟩
  have hareaPos : 0 < ENNReal.ofReal (4 * diameter ^ 2) :=
    ENNReal.ofReal_pos.mpr (by positivity)
  have habsoluteProduct :
      ENNReal.ofReal lineVolume ≤
        volume {t : ℝ | anchor + t • normal ∈ good} *
          ENNReal.ofReal (4 * diameter ^ 2) := by
    calc
      ENNReal.ofReal lineVolume ≤ retainedVolume := hlineFloor
      _ ≤ volume good := hgoodVolume
      _ ≤ ENNReal.ofReal (4 * diameter ^ 2) *
          volume {t : ℝ | anchor + t • normal ∈ good} := hrelativeLine
      _ = volume {t : ℝ | anchor + t • normal ∈ good} *
          ENNReal.ofReal (4 * diameter ^ 2) := mul_comm _ _
  have hline :
      ENNReal.ofReal (lineVolume / (4 * diameter ^ 2)) ≤
        volume {t : ℝ | anchor + t • normal ∈ good} := by
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    exact (ENNReal.div_le_iff hareaPos.ne' ENNReal.ofReal_ne_top).mpr
      habsoluteProduct
  exact ⟨{
    good := good
    good_measurable := hgoodMeasurable
    good_subset := hgoodSubset
    good_volume := hgoodVolume
    center := center
    good_ball := hgoodBall
    normal_unit := hnormal
    anchor := anchor
    anchor_mem := hanchor
    line_volume := hline
    relative_line_volume := hrelativeLine
    full_grain := fun t ht => hfullGrain (anchor + t • normal) ht
  }⟩

/-- Build the full-grain/Fubini certificate for one bounded cell from a
uniform local projection-covering bound at centers of that cell.  The finite
spatial cover has at most `512` centers; `coverBudget` is the caller's exact
integer budget for the resulting union of projected pieces. -/
theorem proposition63_fullGrainFubiniCell_of_localCoverings
    {E : Set Point3} (hE : MeasurableSet E)
    (hEFinite : volume E ≠ ⊤)
    (normal : Point3) (hnormal : ‖normal‖ = 1)
    {rho radius lineVolume : ℝ}
    (hrho : 0 < rho) (hradius : 0 < radius)
    (center : Point3)
    (hEball : E ⊆ Metric.closedBall center (2 * radius))
    (localBound : ENNReal) (hlocalBoundFinite : localBound ≠ ⊤)
    (hlocal : ∀ point ∈ E,
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
        (scalarProjection normal
          (E ∩ Metric.closedBall point radius))) : ENNReal) ≤ localBound)
    (retainedVolume threshold : ENNReal)
    (hretainedFinite : retainedVolume ≠ ⊤)
    (htwice : 2 * retainedVolume ≤ volume E)
    (hlineVolume : 0 < lineVolume)
    (hlineFloor : ENNReal.ofReal lineVolume ≤ retainedVolume)
    (coverBudget : ℕ) (hcoverBudgetPos : 0 < coverBudget)
    (hcoverBudget :
      (512 : ENNReal) * localBound ≤ (coverBudget : ENNReal))
    (hthreshold : threshold =
      retainedVolume / (2 * (coverBudget : ENNReal))) :
    Nonempty (Proposition63FullGrainFubiniCellData E normal rho
      (2 * radius) lineVolume retainedVolume threshold) := by
  rcases Kakeya.Assouad.point3_subset_self_centered_sqrt_cover
      hradius hEball with ⟨centers, hcentersIn, hcentersCard, hspatialCover⟩
  let piece : Point3 → Set ℝ := fun point =>
    scalarProjection normal (E ∩ Metric.closedBall point radius)
  have hprojectionSubset :
      (fun point : Point3 => inner ℝ point normal) '' E ⊆
        ⋃ point ∈ centers, piece point := by
    rintro value ⟨point, hpoint, rfl⟩
    rcases Set.mem_iUnion₂.mp (hspatialCover hpoint) with
      ⟨selectedCenter, hselectedCenter, hpointBall⟩
    exact Set.mem_iUnion₂.mpr
      ⟨selectedCenter, hselectedCenter,
        ⟨point, ⟨hpoint, hpointBall⟩, rfl⟩⟩
  have hpieces : ∀ point ∈ centers,
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
        (piece point)) : ENNReal) ≤ localBound := by
    intro point hpoint
    exact hlocal point (hcentersIn hpoint)
  have hunion :
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
        (⋃ point ∈ centers, piece point)) : ENNReal) ≤
        (centers.card : ENNReal) * localBound :=
    Kakeya.Assouad.externalCoveringNumber_biUnion_le_card hpieces
  have hwhole :
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
        ((fun point : Point3 => inner ℝ point normal) '' E)) : ENNReal) ≤
        (coverBudget : ENNReal) := by
    have hmono :
        (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
          ((fun point : Point3 => inner ℝ point normal) '' E)) : ENNReal) ≤
          (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
            (⋃ point ∈ centers, piece point)) : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set hprojectionSubset
    calc
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
          ((fun point : Point3 => inner ℝ point normal) '' E)) : ENNReal) ≤
          (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
            (⋃ point ∈ centers, piece point)) : ENNReal) := hmono
      _ ≤ (centers.card : ENNReal) * localBound := hunion
      _ ≤ (512 : ENNReal) * localBound := by
        gcongr
        exact_mod_cast hcentersCard
      _ ≤ (coverBudget : ENNReal) := hcoverBudget
  exact proposition63_fullGrainFubiniCell hE hEFinite normal hnormal
    hrho (by positivity : 0 < 2 * radius) center hEball
    retainedVolume threshold hretainedFinite htwice hlineVolume
    hlineFloor coverBudget hcoverBudgetPos hwhole hthreshold

/-- Convert one-scale estimates in the varying plane-map direction into one
uniform covering estimate in the normal at the center of a square-root cell.
The spatial cover is self-centered, so every local estimate is invoked at an
actual point of `E`. -/
theorem proposition63_cell_projection_covering_of_planeMap
    {E : Set Point3}
    {rho radius K : ℝ}
    (hrho : 0 < rho) (hradius : 0 < radius)
    (hradiusSqrt : radius = Real.sqrt rho)
    (center : Point3) (hcenter : center ∈ E)
    (hEball : E ⊆ Metric.closedBall center (2 * radius))
    (planeMap : Point3 → Point3)
    (hK : 1 ≤ K)
    (hlipschitz : ∀ first ∈ E, ∀ second ∈ E,
      dist (planeMap first) (planeMap second) ≤
        K * dist first second)
    (localBound : ENNReal)
    (hlocal : ∀ point ∈ E,
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
        (scalarProjection (planeMap point)
          (E ∩ Metric.closedBall point radius))) : ENNReal) ≤ localBound) :
    (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
      (scalarProjection (planeMap center) E)) : ENNReal) ≤
      (512 : ENNReal) *
        ((2 * Nat.ceil (2 * K) + 2 : ENNReal) * localBound) := by
  rcases Kakeya.Assouad.point3_subset_self_centered_sqrt_cover
      hradius hEball with ⟨centers, hcentersIn, hcentersCard, hcover⟩
  let piece : Point3 → Set ℝ := fun point =>
    scalarProjection (planeMap center)
      (E ∩ Metric.closedBall point radius)
  have hprojectionSubset : scalarProjection (planeMap center) E ⊆
      ⋃ point ∈ centers, piece point := by
    rintro value ⟨point, hpoint, rfl⟩
    rcases Set.mem_iUnion₂.mp (hcover hpoint) with
      ⟨selectedCenter, hselectedCenter, hpointBall⟩
    exact Set.mem_iUnion₂.mpr
      ⟨selectedCenter, hselectedCenter,
        ⟨point, ⟨hpoint, hpointBall⟩, rfl⟩⟩
  have hpiece : ∀ point ∈ centers,
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
        (piece point)) : ENNReal) ≤
        (2 * Nat.ceil (2 * K) + 2 : ENNReal) * localBound := by
    intro point hpoint
    have hpointE : point ∈ E := hcentersIn hpoint
    have hdistance : dist point center ≤ 2 * Real.sqrt rho := by
      have hraw : dist point center ≤ 2 * radius := hEball hpointE
      rwa [hradiusSqrt] at hraw
    have htransfer :=
      Kakeya.Assouad.wz1_lemma18_cell_normal_projection_transfer
        rho radius K hrho hradius.le (by rw [hradiusSqrt]) hK
        E planeMap point center hdistance
        (hlipschitz point hpointE center hcenter)
    have hfactor : (2 * Nat.ceil ((2 * K * rho) / rho) + 2 : ENNReal) =
        (2 * Nat.ceil (2 * K) + 2 : ENNReal) := by
      have hratio : (2 * K * rho) / rho = 2 * K := by
        field_simp [hrho.ne']
      rw [hratio]
    have hlocalBound := mul_le_mul_right (hlocal point hpointE)
      (2 * Nat.ceil ((2 * K * rho) / rho) + 2 : ENNReal)
    have hbound := htransfer.2.trans hlocalBound
    simpa only [piece, hfactor] using hbound
  have hunion := Kakeya.Assouad.externalCoveringNumber_biUnion_le_card
    (ε := Real.toNNReal rho) (s := centers) (A := piece) hpiece
  have hmono :
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
        (scalarProjection (planeMap center) E)) : ENNReal) ≤
        (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
          (⋃ point ∈ centers, piece point)) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set hprojectionSubset
  exact hmono.trans <| hunion.trans <| by
    gcongr
    exact_mod_cast hcentersCard

/-- Cellwise full-grain/Fubini selection from one-scale estimates in the
varying direction of a common Lipschitz plane map. -/
theorem proposition63_fullGrainFubiniCell_of_planeMap
    {E : Set Point3} (hE : MeasurableSet E)
    (hEFinite : volume E ≠ ⊤)
    {rho radius K lineVolume : ℝ}
    (hrho : 0 < rho) (hradius : 0 < radius)
    (hradiusSqrt : radius = Real.sqrt rho)
    (center : Point3) (hcenter : center ∈ E)
    (hEball : E ⊆ Metric.closedBall center (2 * radius))
    (planeMap : Point3 → Point3)
    (hcenterUnit : ‖planeMap center‖ = 1)
    (hK : 1 ≤ K)
    (hlipschitz : ∀ first ∈ E, ∀ second ∈ E,
      dist (planeMap first) (planeMap second) ≤
        K * dist first second)
    (localBound : ENNReal)
    (hlocalBoundFinite : localBound ≠ ⊤)
    (hlocal : ∀ point ∈ E,
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
        (scalarProjection (planeMap point)
          (E ∩ Metric.closedBall point radius))) : ENNReal) ≤ localBound)
    (retainedVolume threshold : ENNReal)
    (hretainedFinite : retainedVolume ≠ ⊤)
    (htwice : 2 * retainedVolume ≤ volume E)
    (hlineVolume : 0 < lineVolume)
    (hlineFloor : ENNReal.ofReal lineVolume ≤ retainedVolume)
    (coverBudget : ℕ) (hcoverBudgetPos : 0 < coverBudget)
    (hcoverBudget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * K) + 2 : ENNReal) * localBound) ≤
        (coverBudget : ENNReal))
    (hthreshold : threshold =
      retainedVolume / (2 * (coverBudget : ENNReal))) :
    Nonempty (Proposition63FullGrainFubiniCellData E (planeMap center)
      rho (2 * radius) lineVolume retainedVolume threshold) := by
  have hwhole := proposition63_cell_projection_covering_of_planeMap
    hrho hradius hradiusSqrt center hcenter hEball planeMap hK
    hlipschitz localBound hlocal
  exact proposition63_fullGrainFubiniCell hE hEFinite
    (planeMap center) hcenterUnit hrho (by positivity : 0 < 2 * radius)
    center hEball retainedVolume threshold hretainedFinite htwice
    hlineVolume hlineFloor coverBudget hcoverBudgetPos
    (hwhole.trans hcoverBudget) hthreshold

end Kakeya.Assouad.PureWZ2

end
