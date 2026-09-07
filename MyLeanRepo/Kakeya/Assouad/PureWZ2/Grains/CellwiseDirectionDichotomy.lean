import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DirectionClusterPlane
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.TransversePairPaper
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ExtremalCWATransfer
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperCubicalRefinement

/-!
# Cellwise sparse-close / dense-close direction dichotomy

On a cubical shading, the active tube set and every close-direction count are
constant on a fine grid cell.  We therefore split whole cells according to
whether some direction contains more than half of a prescribed multiplicity
threshold in its close cluster.

* On sparse cells, every active tube has close count at most half the
  threshold; this is exactly the transverse-pair input.
* On dense cells, choose a cluster center cellwise and retain the entire close
  cluster.  Under the dyadic upper multiplicity bound, at least one quarter
  of the pointwise multiplicity survives, and the center's canonical unit
  normal has incidence at most the cluster radius.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset
open InnerProductGeometry

attribute [local instance] Classical.propDecidable

/-- Close-direction count is constant on the cells of a cubical shading. -/
lemma paperCloseDirectionCount_eq_of_same_cell
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hcubical : WZ1PaperIsCubicalShading S)
    (center : Fin F.card) (kappa : ℝ)
    {first second : Point3}
    (hsame : wz1PaperGridIndex delta first =
      wz1PaperGridIndex delta second) :
    paperCloseDirectionCount S first center kappa =
      paperCloseDirectionCount S second center kappa := by
  unfold paperCloseDirectionCount
  congr 1
  apply Finset.filter_congr
  intro index _
  rw [hcubical.carrier_mem_iff_of_same_cell index hsame]

/-- Close-direction count is measurable as a finite sum of carrier
indicators. -/
lemma paperCloseDirectionCount_measurable
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (S : WZ1PaperTubeShading F) (center : Fin F.card) (kappa : ℝ) :
    Measurable fun point => paperCloseDirectionCount S point center kappa := by
  have heq : (fun point => paperCloseDirectionCount S point center kappa) =
      fun point => ∑ other : Fin F.card,
        if point ∈ S.carrier other ∧
            ‖wz1Cross (F.tube center).direction
              (F.tube other).direction‖ < kappa
        then 1 else 0 := by
    funext point
    unfold paperCloseDirectionCount
    rw [Finset.card_filter]
    rfl
  rw [heq]
  apply Finset.measurable_sum
  intro other _
  by_cases hdirection : ‖wz1Cross (F.tube center).direction
      (F.tube other).direction‖ < kappa
  · have hpredicate : MeasurableSet {point | point ∈ S.carrier other ∧
        ‖wz1Cross (F.tube center).direction
          (F.tube other).direction‖ < kappa} := by
      simpa [hdirection] using S.measurable_carrier other
    exact measurable_const.ite hpredicate measurable_const
  · simp [hdirection]

/-- Whole cells on which some active tube carries a close cluster larger than
half the prescribed multiplicity threshold. -/
def denseCloseCellSet
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (S : WZ1PaperTubeShading F) (kappa : ℝ) (m : ℕ) : Set Point3 :=
  {point | point ∈ S.union ∧
    ∃ center : Fin F.card, point ∈ S.carrier center ∧
      m < 2 * paperCloseDirectionCount S point center kappa}

/-- The dense-close set is measurable. -/
lemma denseCloseCellSet_measurable
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (S : WZ1PaperTubeShading F) (kappa : ℝ) (m : ℕ) :
    MeasurableSet (denseCloseCellSet S kappa m) := by
  let closeSet (center other : Fin F.card) : Set Point3 :=
    S.carrier center ∩ S.carrier other
  have hclose : ∀ center other, MeasurableSet (closeSet center other) :=
    fun center other => (S.measurable_carrier center).inter
      (S.measurable_carrier other)
  have hcenter : ∀ center : Fin F.card, MeasurableSet
      {point | point ∈ S.carrier center ∧
        m < 2 * paperCloseDirectionCount S point center kappa} := by
    intro center
    exact (S.measurable_carrier center).inter <|
      measurableSet_lt measurable_const
        (measurable_const.mul
          (paperCloseDirectionCount_measurable S center kappa))
  have hunion : MeasurableSet S.union := measurableSet_shading_union S
  have heq : denseCloseCellSet S kappa m = S.union ∩
      ⋃ center : Fin F.card,
        {point | point ∈ S.carrier center ∧
          m < 2 * paperCloseDirectionCount S point center kappa} := by
    ext point
    simp [denseCloseCellSet]
  rw [heq]
  exact hunion.inter (MeasurableSet.iUnion hcenter)

/-- Cubicality makes the dense-close predicate constant on each fine cell. -/
lemma denseCloseCellSet_cube_union
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hcubical : WZ1PaperIsCubicalShading S)
    (kappa : ℝ) (m : ℕ) :
    ∀ point ∈ denseCloseCellSet S kappa m,
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
        denseCloseCellSet S kappa m := by
  intro point hpoint other hother
  rcases hpoint with ⟨hpointUnion, center, hcenter, hlarge⟩
  have hcell : wz1PaperGridIndex delta other =
      wz1PaperGridIndex delta point :=
    (mem_wz1PaperGridCube delta
      (wz1PaperGridIndex delta point) other).mp hother
  have hcarrier : ∀ index : Fin F.card,
      point ∈ S.carrier index ↔ other ∈ S.carrier index :=
    fun index => hcubical.carrier_mem_iff_of_same_cell index hcell.symm
  have hcount : paperCloseDirectionCount S point center kappa =
      paperCloseDirectionCount S other center kappa := by
    unfold paperCloseDirectionCount
    congr 1
    apply Finset.filter_congr
    intro index _
    simp only [hcarrier index]
  have hotherUnion : other ∈ S.union := by
    rcases hpointUnion with ⟨index, hindex⟩
    exact ⟨index, (hcarrier index).mp hindex⟩
  exact ⟨hotherUnion, center, (hcarrier center).mp hcenter, by simpa [← hcount]
    using hlarge⟩

/-- The complementary sparse-close cells are also a union of whole fine
cells. -/
lemma sparseCloseCellSet_cube_union
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hcubical : WZ1PaperIsCubicalShading S)
    (kappa : ℝ) (m : ℕ) :
    ∀ point ∈ (denseCloseCellSet S kappa m)ᶜ,
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
        (denseCloseCellSet S kappa m)ᶜ := by
  intro point hpoint other hother hotherDense
  have hcell : wz1PaperGridIndex delta point =
      wz1PaperGridIndex delta other :=
    (mem_wz1PaperGridCube delta
      (wz1PaperGridIndex delta point) other).mp hother |>.symm
  have hpointCube : point ∈
      wz1PaperGridCube delta (wz1PaperGridIndex delta other) :=
    (mem_wz1PaperGridCube delta
      (wz1PaperGridIndex delta other) point).mpr hcell
  exact hpoint ((denseCloseCellSet_cube_union hcubical kappa m)
    other hotherDense hpointCube)

/-- Paper-shading restriction to a measurable set and its complement split
the shaded mass exactly. -/
lemma paper_restriction_compl_mass_split
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (S : WZ1PaperTubeShading F) (E : Set Point3)
    (hE : MeasurableSet E) :
    S.mass =
      (paperRestrictShadingToSet S E hE).mass +
      (paperRestrictShadingToSet S Eᶜ hE.compl).mass := by
  rw [paperMassRestrictShadingToSet hE,
    paperMassRestrictShadingToSet hE.compl]
  rw [← lintegral_union hE.compl disjoint_compl_right]
  simp [lintegral_pointMultiplicity]

/-- One of the dense-close and sparse-close whole-cell restrictions retains
at least half the original shaded mass. -/
lemma dense_or_sparse_close_mass
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (S : WZ1PaperTubeShading F) (kappa : ℝ) (m : ℕ) :
    let dense := denseCloseCellSet S kappa m
    let hDense := denseCloseCellSet_measurable S kappa m
    let denseShading := paperRestrictShadingToSet S dense hDense
    let sparseShading := paperRestrictShadingToSet S denseᶜ hDense.compl
    (1 / 2 : ENNReal) * S.mass ≤ denseShading.mass ∨
      (1 / 2 : ENNReal) * S.mass ≤ sparseShading.mass := by
  dsimp only
  let dense := denseCloseCellSet S kappa m
  let hDense := denseCloseCellSet_measurable S kappa m
  let denseShading := paperRestrictShadingToSet S dense hDense
  let sparseShading := paperRestrictShadingToSet S denseᶜ hDense.compl
  have hsplit : S.mass = denseShading.mass + sparseShading.mass := by
    exact paper_restriction_compl_mass_split S dense hDense
  have hS_top : S.mass ≠ ⊤ := by
    simp only [Kakeya.Streamlined.Shading.mass, ENNReal.sum_ne_top]
    intro index _
    have hle : volume (S.carrier index) ≤
        volume (Kakeya.Streamlined.axisBox 2 2 2) :=
      measure_mono <| (S.subset_body index).trans Set.inter_subset_right
    have hbox : volume (Kakeya.Streamlined.axisBox 2 2 2) ≠ ⊤ := by
      have hclosed : IsClosed (Kakeya.Streamlined.axisBox 2 2 2) := by
        have h : ∀ (coordinate : Fin 3),
            IsClosed {point : Point3 | |point coordinate| ≤ 1} := by
          intro coordinate
          have hcont : Continuous fun point : Point3 => point coordinate :=
            PiLp.continuous_apply 2 (fun _ => ℝ) coordinate
          exact isClosed_le (continuous_abs.comp hcont) continuous_const
        have heq : Kakeya.Streamlined.axisBox 2 2 2 =
            {point | |point 0| ≤ 1} ∩
              ({point | |point 1| ≤ 1} ∩
                {point | |point 2| ≤ 1}) := by
          ext point
          simp [Kakeya.Streamlined.axisBox]
        rw [heq]
        exact (h 0).inter ((h 1).inter (h 2))
      have hsub : Kakeya.Streamlined.axisBox 2 2 2 ⊆
          Metric.closedBall (0 : Point3) (Real.sqrt 3) := by
        intro point hpoint
        have hcoordinates :
            |point 0| ≤ 1 ∧ |point 1| ≤ 1 ∧ |point 2| ≤ 1 := by
          simpa [Kakeya.Streamlined.axisBox] using hpoint
        have hsquares : ∀ coordinate : Fin 3, (point coordinate) ^ 2 ≤ 1 := by
          intro coordinate
          have hcoordinate : |point coordinate| ≤ 1 := by
            fin_cases coordinate <;> simp [hcoordinates] <;> linarith
          nlinarith [abs_le.mp hcoordinate]
        have hsum : ∑ coordinate : Fin 3, (point coordinate) ^ 2 ≤ 3 := by
          calc
            ∑ coordinate : Fin 3, (point coordinate) ^ 2 ≤
                ∑ _coordinate : Fin 3, (1 : ℝ) := by
              apply Finset.sum_le_sum
              intro coordinate _
              exact hsquares coordinate
            _ = 3 := by simp
        have hnorm : ‖point‖ ≤ Real.sqrt 3 := by
          rw [EuclideanSpace.norm_eq]
          apply Real.sqrt_le_sqrt
          have heq : ∑ coordinate : Fin 3, ‖point coordinate‖ ^ 2 =
              ∑ coordinate : Fin 3, (point coordinate) ^ 2 := by
            apply Finset.sum_congr rfl
            intro coordinate _
            simp [sq_abs]
          rw [heq]
          exact hsum
        simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
      have hbounded : Bornology.IsBounded
          (Kakeya.Streamlined.axisBox 2 2 2) :=
        Metric.isBounded_closedBall.subset hsub
      exact (Metric.isCompact_of_isClosed_isBounded
        hclosed hbounded).measure_lt_top.ne
    exact ne_top_of_le_ne_top hbox hle
  have hdenseTop : denseShading.mass ≠ ⊤ := by
    by_contra htop
    have : denseShading.mass + sparseShading.mass = ⊤ := by simp [htop]
    exact hS_top (hsplit.trans this)
  have hsparseTop : sparseShading.mass ≠ ⊤ := by
    by_contra htop
    have : denseShading.mass + sparseShading.mass = ⊤ := by simp [htop]
    exact hS_top (hsplit.trans this)
  have hhalfTop : (1 / 2 : ENNReal) * S.mass ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) hS_top
  by_cases hdense : (1 / 2 : ENNReal) * S.mass ≤ denseShading.mass
  · exact Or.inl hdense
  · right
    by_contra hsparse
    have hdenseLt : denseShading.mass < (1 / 2 : ENNReal) * S.mass :=
      lt_of_not_ge hdense
    have hsparseLt : sparseShading.mass < (1 / 2 : ENNReal) * S.mass :=
      lt_of_not_ge hsparse
    have hsum : denseShading.mass + sparseShading.mass < S.mass := by
      calc
        denseShading.mass + sparseShading.mass <
            (1 / 2 : ENNReal) * S.mass + sparseShading.mass :=
          ENNReal.add_lt_add_right
            hsparseTop
            hdenseLt
        _ < (1 / 2 : ENNReal) * S.mass +
            (1 / 2 : ENNReal) * S.mass :=
          ENNReal.add_lt_add_left hhalfTop hsparseLt
        _ = S.mass := by
          rw [← add_mul]
          have hhalf : (1 / 2 : ENNReal) + (1 / 2 : ENNReal) = 1 := by
            have htwo : (2 : ENNReal) ≠ 0 := by norm_num
            have htwoTop : (2 : ENNReal) ≠ ⊤ := by norm_num
            have hinv : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 :=
              ENNReal.mul_inv_cancel htwo htwoTop
            simpa [one_div, two_mul] using hinv
          rw [hhalf, one_mul]
    rw [hsplit] at hsum
    exact lt_irrefl _ hsum

/-- On the dense-close restriction, choose a close-cluster center constantly
on every fine cell. -/
lemma dense_close_cellwise_center
    {delta kappa : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hcubical : WZ1PaperIsCubicalShading S)
    (hF : F.Nonempty) (m : ℕ) :
    let dense := denseCloseCellSet S kappa m
    let hDense := denseCloseCellSet_measurable S kappa m
    let denseShading := paperRestrictShadingToSet S dense hDense
    ∃ center : Point3 → Fin F.card,
      Measurable center ∧
      (∀ point ∈ denseShading.union,
        point ∈ S.carrier (center point) ∧
        m < 2 * paperCloseDirectionCount S point (center point) kappa) ∧
      (∀ first second,
        wz1PaperGridIndex delta first =
          wz1PaperGridIndex delta second →
        center first = center second) := by
  dsimp only
  let dense := denseCloseCellSet S kappa m
  let hDense := denseCloseCellSet_measurable S kappa m
  let denseShading := paperRestrictShadingToSet S dense hDense
  let defaultCenter : Fin F.card := ⟨0, hF⟩
  let P (point : Point3) (center : Fin F.card) : Prop :=
    (point ∈ dense ∧ point ∈ S.carrier center ∧
      m < 2 * paperCloseDirectionCount S point center kappa) ∨
    (point ∉ dense ∧ center = defaultCenter)
  have hP_meas : ∀ center : Fin F.card, MeasurableSet {point | P point center} := by
    intro center
    have hlarge : MeasurableSet {point |
        m < 2 * paperCloseDirectionCount S point center kappa} :=
      measurableSet_lt measurable_const <|
        measurable_const.mul <|
          paperCloseDirectionCount_measurable S center kappa
    by_cases hcenter : center = defaultCenter
    · have heq : {point | P point center} =
          (dense ∩ S.carrier center ∩
            {point | m < 2 * paperCloseDirectionCount S point center kappa}) ∪
          denseᶜ := by
        ext point
        simp [P, hcenter]
        tauto
      rw [heq]
      exact ((hDense.inter (S.measurable_carrier center)).inter hlarge).union
        hDense.compl
    · have heq : {point | P point center} =
          dense ∩ S.carrier center ∩
            {point | m < 2 * paperCloseDirectionCount S point center kappa} := by
        ext point
        simp [P, hcenter]
        tauto
      rw [heq]
      exact (hDense.inter (S.measurable_carrier center)).inter hlarge
  have hP_nonempty : ∀ point, ∃ center, P point center := by
    intro point
    by_cases hpoint : point ∈ dense
    · rcases hpoint with ⟨hunion, center, hcenter, hlarge⟩
      exact ⟨center, Or.inl
        ⟨⟨hunion, center, hcenter, hlarge⟩, hcenter, hlarge⟩⟩
    · exact ⟨defaultCenter, Or.inr ⟨hpoint, rfl⟩⟩
  let candidates (point : Point3) : Finset (Fin F.card) :=
    Finset.univ.filter fun candidate => P point candidate
  have hcandidatesNonempty : ∀ point, (candidates point).Nonempty := by
    intro point
    rcases hP_nonempty point with ⟨candidate, hcandidate⟩
    exact ⟨candidate, Finset.mem_filter.mpr
      ⟨Finset.mem_univ candidate, hcandidate⟩⟩
  let center (point : Point3) : Fin F.card :=
    (candidates point).min' (hcandidatesNonempty point)
  have hcenterSpec : ∀ point, P point (center point) := by
    intro point
    exact (Finset.mem_filter.mp
      (Finset.min'_mem (candidates point) (hcandidatesNonempty point))).2
  have hcenterMeasurable : Measurable center := by
    apply measurable_of_measurable_fibers
    intro candidate
    have hfiber : center ⁻¹' {candidate} =
        {point | P point candidate} ∩
          {point | ∀ previous : Fin F.card, previous < candidate →
            ¬P point previous} := by
      ext point
      simp only [Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · intro hcenterEq
        constructor
        · rw [← hcenterEq]
          exact hcenterSpec point
        · intro previous hprevious hPprevious
          have hpreviousMem : previous ∈ candidates point :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPprevious⟩
          have hle : center point ≤ previous := by
            exact Finset.min'_le (candidates point) previous hpreviousMem
          rw [hcenterEq] at hle
          exact (not_le_of_gt hprevious) hle
      · rintro ⟨hPcand, hprevious⟩
        have hcandMem : candidate ∈ candidates point :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPcand⟩
        have hle : center point ≤ candidate :=
          Finset.min'_le (candidates point) candidate hcandMem
        exact le_antisymm hle <| by
          by_contra hnot
          have hlt : center point < candidate := lt_of_not_ge hnot
          exact hprevious (center point) hlt (hcenterSpec point)
    rw [hfiber]
    apply (hP_meas candidate).inter
    have heq : {point | ∀ previous : Fin F.card, previous < candidate →
        ¬P point previous} =
        ⋂ previous ∈ (Finset.univ.filter fun previous : Fin F.card =>
          previous < candidate), {point | ¬P point previous} := by
      ext point
      simp
    rw [heq]
    exact Finset.measurableSet_biInter _ fun previous _ =>
      (hP_meas previous).compl
  have hcenterDense : ∀ point ∈ denseShading.union,
      point ∈ S.carrier (center point) ∧
      m < 2 * paperCloseDirectionCount S point (center point) kappa := by
    intro point hpoint
    have hpointDense : point ∈ dense := by
      rcases hpoint with ⟨index, hindex⟩
      exact hindex.2
    rcases hcenterSpec point with hgood | hbad
    · exact hgood.2
    · exact False.elim (hbad.1 hpointDense)
  have hcenterCell : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        center first = center second := by
    intro first second hcell
    have hdenseIff : first ∈ dense ↔ second ∈ dense := by
      constructor
      · intro hfirst
        apply denseCloseCellSet_cube_union hcubical kappa m first hfirst
        exact (mem_wz1PaperGridCube delta
          (wz1PaperGridIndex delta first) second).mpr hcell.symm
      · intro hsecond
        apply denseCloseCellSet_cube_union hcubical kappa m second hsecond
        exact (mem_wz1PaperGridCube delta
          (wz1PaperGridIndex delta second) first).mpr hcell
    have hPiff : ∀ candidate : Fin F.card,
        P first candidate ↔ P second candidate := by
      intro candidate
      simp only [P]
      have hcarrier := hcubical.carrier_mem_iff_of_same_cell candidate hcell
      have hcount := paperCloseDirectionCount_eq_of_same_cell
        hcubical candidate kappa hcell
      rw [hcarrier, hcount, hdenseIff]
    apply le_antisymm
    · apply Finset.min'_le
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (hPiff (center second)).mpr (hcenterSpec second)⟩
    · apply Finset.min'_le
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (hPiff (center first)).mp (hcenterSpec first)⟩
  exact ⟨center, hcenterMeasurable, hcenterDense, hcenterCell⟩

/-- A close-direction condition whose center is selected measurably from a
finite tube family is measurable. -/
lemma measurable_cellwise_close_direction
    {delta kappa : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {center : Point3 → Fin F.card}
    (hcenter : Measurable center) (index : Fin F.card) :
    MeasurableSet {point |
      ‖wz1Cross (F.tube (center point)).direction
        (F.tube index).direction‖ < kappa} := by
  have hfinite : Measurable fun candidate : Fin F.card =>
      ‖wz1Cross (F.tube candidate).direction
        (F.tube index).direction‖ :=
    measurable_of_finite (fun candidate : Fin F.card =>
      ‖wz1Cross (F.tube candidate).direction
        (F.tube index).direction‖)
  exact measurableSet_lt (hfinite.comp hcenter) measurable_const

/-- On the dense-close cells, retain the selected close cluster.  The
resulting shading is cubical, its canonical normal is a genuine cellwise
weak plane map, and a dyadic upper multiplicity bound pays only a factor four
in shaded mass. -/
theorem dense_close_plane_map_refinement
    {delta kappa : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hcubical : WZ1PaperIsCubicalShading S)
    (hF : F.Nonempty) (m : ℕ)
    (hmultUpper : ∀ point ∈ S.union,
      S.pointMultiplicity point < 2 * m) :
    let dense := denseCloseCellSet S kappa m
    let hDense := denseCloseCellSet_measurable S kappa m
    let denseShading := paperRestrictShadingToSet S dense hDense
    ∃ (center : Point3 → Fin F.card)
      (selected : WZ1PaperTubeShading F)
      (planeMap : PaperWZ1WeakPlaneMapData selected kappa),
      Measurable center ∧
      PaperIsSubshading selected denseShading ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ index point, point ∈ selected.carrier index →
        ‖wz1Cross (F.tube (center point)).direction
          (F.tube index).direction‖ < kappa) ∧
      (∀ first second,
        wz1PaperGridIndex delta first =
          wz1PaperGridIndex delta second →
        center first = center second) ∧
      (∀ point ∈ denseShading.union,
        m < 2 * selected.pointMultiplicity point) ∧
      (∀ first second,
        wz1PaperGridIndex delta first =
          wz1PaperGridIndex delta second →
        planeMap.planeMap first = planeMap.planeMap second) ∧
      (1 / 4 : ENNReal) * denseShading.mass ≤ selected.mass := by
  dsimp only
  let dense := denseCloseCellSet S kappa m
  let hDense := denseCloseCellSet_measurable S kappa m
  let denseShading := paperRestrictShadingToSet S dense hDense
  have hcenterData := dense_close_cellwise_center
    (S := S) (kappa := kappa) hcubical hF m
  dsimp only at hcenterData
  rcases hcenterData with
    ⟨center, hcenterMeasurable, hcenterDense, hcenterCell⟩
  let selected : WZ1PaperTubeShading F :=
    { carrier := fun index =>
        {point | point ∈ denseShading.carrier index ∧
          ‖wz1Cross (F.tube (center point)).direction
            (F.tube index).direction‖ < kappa}
      measurable_carrier := fun index =>
        (denseShading.measurable_carrier index).inter
          (measurable_cellwise_close_direction
            hcenterMeasurable index)
      subset_body := fun index point hpoint =>
        denseShading.subset_body index hpoint.1 }
  have hdenseCubical : WZ1PaperIsCubicalShading denseShading :=
    paperRestrictShadingToSet_cubical hDense hcubical
      (denseCloseCellSet_cube_union hcubical kappa m)
  have hselectedSub : PaperIsSubshading selected denseShading := by
    intro index point hpoint
    exact hpoint.1
  have hselectedCubical : WZ1PaperIsCubicalShading selected := by
    intro index point hpoint other hother
    have hcell : wz1PaperGridIndex delta other =
        wz1PaperGridIndex delta point :=
      (mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) other).mp hother
    have hcarrier : other ∈ denseShading.carrier index :=
      hdenseCubical index point hpoint.1 hother
    have hcenterEq : center other = center point :=
      hcenterCell other point hcell
    exact ⟨hcarrier, by simpa [hcenterEq] using hpoint.2⟩
  have hselectedCluster : ∀ index point,
      point ∈ selected.carrier index →
      ‖wz1Cross (F.tube (center point)).direction
        (F.tube index).direction‖ < kappa := by
    intro index point hpoint
    exact hpoint.2
  let planeMap : PaperWZ1WeakPlaneMapData selected kappa :=
    { planeMap := fun point =>
        orthogonalNormal (F.tube (center point)).direction
      measurable := by
        have hfinite : Measurable fun candidate : Fin F.card =>
            orthogonalNormal (F.tube candidate).direction :=
          measurable_of_finite (fun candidate : Fin F.card =>
            orthogonalNormal (F.tube candidate).direction)
        exact hfinite.comp hcenterMeasurable
      unit := by
        intro point _
        exact orthogonalNormal_unit (F.tube (center point)).direction
      incidence := by
        intro index point hpoint
        exact orthogonalNormal_incidence_of_cross_lt
          (F.tube (center point)).direction
          (F.tube index).direction
          (F.tube (center point)).direction_unit
          (F.tube index).direction_unit hpoint.2 }
  have hmultiplicity : ∀ point ∈ denseShading.union,
      m < 2 * selected.pointMultiplicity point := by
    intro point hpoint
    have hpointDense : point ∈ dense := by
      rcases hpoint with ⟨index, hindex⟩
      exact hindex.2
    have hlarge := (hcenterDense point hpoint).2
    have heq : paperCloseDirectionCount S point (center point) kappa =
        selected.pointMultiplicity point := by
      simp only [paperCloseDirectionCount,
        Kakeya.Streamlined.Shading.pointMultiplicity]
      congr 1
      apply Finset.ext
      intro index
      simp [selected, denseShading, paperRestrictShadingToSet,
        hpointDense]
    rwa [heq] at hlarge
  have hmassMultiplicity : ∀ point ∈ denseShading.union,
      denseShading.pointMultiplicity point ≤
        4 * selected.pointMultiplicity point := by
    intro point hpoint
    have hpointDense : point ∈ dense := by
      rcases hpoint with ⟨index, hindex⟩
      exact hindex.2
    have hpointS : point ∈ S.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, hindex.1⟩
    have hdenseMultiplicity : denseShading.pointMultiplicity point =
        S.pointMultiplicity point :=
      paperPmRestrictShadingToSet hDense hpointDense
    have hupper := hmultUpper point hpointS
    have hlower := hmultiplicity point hpoint
    omega
  have hmass : (1 / 4 : ENNReal) * denseShading.mass ≤ selected.mass :=
    paper_mass_lower_from_pointMultiplicity hmassMultiplicity
  have hplaneCell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      planeMap.planeMap first = planeMap.planeMap second := by
    intro first second hcell
    exact congrArg
      (fun index : Fin F.card =>
        orthogonalNormal (F.tube index).direction)
      (hcenterCell first second hcell)
  exact ⟨center, selected, planeMap, hcenterMeasurable, hselectedSub,
    hselectedCubical, hselectedCluster, hcenterCell, hmultiplicity,
    hplaneCell, hmass⟩

/-- On the complementary sparse-close cells, every active tube sees at most
half the prescribed multiplicity threshold in its close cluster.  The bound
is stated for the restricted shading itself, exactly as required by the
transverse-pair count. -/
theorem sparse_close_cellwise_refinement
    {delta kappa : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hcubical : WZ1PaperIsCubicalShading S) (m : ℕ) :
    let dense := denseCloseCellSet S kappa m
    let hDense := denseCloseCellSet_measurable S kappa m
    let sparseShading := paperRestrictShadingToSet S denseᶜ hDense.compl
    PaperIsSubshading sparseShading S ∧
    WZ1PaperIsCubicalShading sparseShading ∧
    ∀ point ∈ sparseShading.union, ∀ index,
      point ∈ sparseShading.carrier index →
      2 * paperCloseDirectionCount sparseShading point index kappa ≤ m := by
  dsimp only
  let dense := denseCloseCellSet S kappa m
  let hDense := denseCloseCellSet_measurable S kappa m
  let sparseShading := paperRestrictShadingToSet S denseᶜ hDense.compl
  have hsub : PaperIsSubshading sparseShading S := by
    intro index point hpoint
    exact hpoint.1
  have hcubicalSparse : WZ1PaperIsCubicalShading sparseShading :=
    paperRestrictShadingToSet_cubical hDense.compl hcubical
      (sparseCloseCellSet_cube_union hcubical kappa m)
  refine ⟨hsub, hcubicalSparse, ?_⟩
  intro point hpoint index hindex
  have hpointSparse : point ∉ dense := hindex.2
  have hindexS : point ∈ S.carrier index := hindex.1
  have hcountS : 2 * paperCloseDirectionCount S point index kappa ≤ m := by
    by_contra hnot
    have hlarge : m <
        2 * paperCloseDirectionCount S point index kappa :=
      lt_of_not_ge hnot
    exact hpointSparse ⟨⟨index, hindexS⟩, index, hindexS, hlarge⟩
  have hcountMono : paperCloseDirectionCount sparseShading point index kappa ≤
      paperCloseDirectionCount S point index kappa := by
    unfold paperCloseDirectionCount
    apply Finset.card_le_card
    intro other hother
    simp only [Finset.mem_filter] at hother ⊢
    exact ⟨hother.1, hother.2.1.1, hother.2.2⟩
  change 2 * paperCloseDirectionCount sparseShading point index kappa ≤ m
  exact (Nat.mul_le_mul_left 2 hcountMono).trans hcountS

/-- Cubical direction dichotomy at one threshold.  Either a dense-close
whole-cell part retains half the mass and yields a further one-quarter-mass
cellwise plane-map refinement, or the sparse-close whole-cell part retains
half the mass and satisfies the transverse close-count bound everywhere. -/
theorem dense_or_sparse_close_refinement
    {delta kappa : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hcubical : WZ1PaperIsCubicalShading S)
    (hF : F.Nonempty) (m : ℕ)
    (hmultUpper : ∀ point ∈ S.union,
      S.pointMultiplicity point < 2 * m) :
    let dense := denseCloseCellSet S kappa m
    let hDense := denseCloseCellSet_measurable S kappa m
    let denseShading := paperRestrictShadingToSet S dense hDense
    let sparseShading := paperRestrictShadingToSet S denseᶜ hDense.compl
    ((1 / 2 : ENNReal) * S.mass ≤ denseShading.mass ∧
      ∃ (center : Point3 → Fin F.card)
        (selected : WZ1PaperTubeShading F)
        (planeMap : PaperWZ1WeakPlaneMapData selected kappa),
        Measurable center ∧
        PaperIsSubshading selected denseShading ∧
        WZ1PaperIsCubicalShading selected ∧
        (∀ index point, point ∈ selected.carrier index →
          ‖wz1Cross (F.tube (center point)).direction
            (F.tube index).direction‖ < kappa) ∧
        (∀ first second,
          wz1PaperGridIndex delta first =
            wz1PaperGridIndex delta second →
          center first = center second) ∧
        (∀ point ∈ denseShading.union,
          m < 2 * selected.pointMultiplicity point) ∧
        (∀ first second,
          wz1PaperGridIndex delta first =
            wz1PaperGridIndex delta second →
          planeMap.planeMap first = planeMap.planeMap second) ∧
        (1 / 4 : ENNReal) * denseShading.mass ≤ selected.mass) ∨
    ((1 / 2 : ENNReal) * S.mass ≤ sparseShading.mass ∧
      PaperIsSubshading sparseShading S ∧
      WZ1PaperIsCubicalShading sparseShading ∧
      ∀ point ∈ sparseShading.union, ∀ index,
        point ∈ sparseShading.carrier index →
        2 * paperCloseDirectionCount sparseShading point index kappa ≤ m) := by
  dsimp only
  rcases dense_or_sparse_close_mass S kappa m with hdense | hsparse
  · left
    exact ⟨hdense, dense_close_plane_map_refinement
      hcubical hF m hmultUpper⟩
  · right
    exact ⟨hsparse, sparse_close_cellwise_refinement hcubical m⟩

end Kakeya.Assouad.PureWZ2

end
