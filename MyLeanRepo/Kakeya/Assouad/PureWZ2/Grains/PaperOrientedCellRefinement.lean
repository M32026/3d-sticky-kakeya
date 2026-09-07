import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CellwiseFiniteLabelMassRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.GridCovering
import MyLeanRepo.Kakeya.Assouad.WZ1.MeasurableFiniteChoice
import MyLeanRepo.Kakeya.Assouad.WZ1.PlaneProjectionPerturbation

/-!
# Oriented finite-cap refinement for paper shadings

This is the paper-shading form of the final pigeonhole in WZ1 Lemma 13.
It keeps the supplied plane map and selects one directed coordinate cap in
each finite spatial cell.  The generic cellwise-label theorem supplies the
mass bookkeeping.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

theorem paper_oriented_cell_refinement
    {delta kappa incidence scale : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Cell : Type*}
    [Countable Cell] [DecidableEq Cell]
    [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
    (S : WZ1PaperTubeShading F)
    (hSCubical : WZ1PaperIsCubicalShading S)
    (planeMap : Point3 → Point3) (hplaneMap : Measurable planeMap)
    (cell : Point3 → Cell) (hcell : Measurable cell)
    (hcellFine : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      cell first = cell second)
    (hplaneFine : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      planeMap first = planeMap second)
    (activeCells : Finset Cell)
    (hsupport : ∀ p ∈ S.union, cell p ∈ activeCells)
    (firstDirection secondDirection : Cell → Point3)
    (hkappa : 0 < kappa) (hincidence : 0 ≤ incidence)
    (hscale : 0 < scale)
    (hfirstUnit : ∀ c, ‖firstDirection c‖ = 1)
    (hsecondUnit : ∀ c, ‖secondDirection c‖ = 1)
    (htransverse : ∀ c ∈ activeCells,
      kappa ≤ ‖wz1Cross (firstDirection c) (secondDirection c)‖)
    (hplaneUnit : ∀ p ∈ S.union, ‖planeMap p‖ = 1)
    (hfirstIncidence : ∀ p ∈ S.union,
      |inner ℝ (planeMap p) (firstDirection (cell p))| ≤ incidence)
    (hsecondIncidence : ∀ p ∈ S.union,
      |inner ℝ (planeMap p) (secondDirection (cell p))| ≤ incidence) :
    ∃ (selected : WZ1PaperTubeShading F),
      PaperIsSubshading selected S ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ p ∈ selected.union, ∀ q ∈ selected.union,
        cell p = cell q → dist (planeMap p) (planeMap q) ≤ scale) ∧
      (∀ p ∈ selected.union,
        selected.pointMultiplicity p = S.pointMultiplicity p) ∧
      S.mass ≤
        (wz1OrientationCapCount (10 * incidence / kappa) scale : ENNReal) *
          selected.mass := by
  classical
  let radius : ℝ := 10 * incidence / kappa
  have hradius : 0 ≤ radius := by
    dsimp only [radius]
    positivity
  let N : ℕ := Nat.ceil (2 * Real.sqrt 3 * radius / scale) + 1
  have hN : 1 ≤ N := by
    dsimp only [N]
    omega
  have hdiam : Real.sqrt 3 * (2 * radius / N) ≤ scale := by
    have hceil :
        2 * Real.sqrt 3 * radius / scale ≤
          (Nat.ceil (2 * Real.sqrt 3 * radius / scale) : ℝ) :=
      Nat.le_ceil _
    have hNstrict :
        2 * Real.sqrt 3 * radius / scale < (N : ℝ) := by
      dsimp only [N]
      have hsucc :
          (Nat.ceil (2 * Real.sqrt 3 * radius / scale) : ℝ) <
            (Nat.ceil (2 * Real.sqrt 3 * radius / scale) + 1 : ℕ) := by
        simp
      exact hceil.trans_lt hsucc
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
    have hmul : 2 * Real.sqrt 3 * radius < (N : ℝ) * scale := by
      calc
        2 * Real.sqrt 3 * radius =
            (2 * Real.sqrt 3 * radius / scale) * scale := by
              field_simp [hscale.ne'] <;> ring
        _ < (N : ℝ) * scale := by gcongr
    have hdiv : 2 * Real.sqrt 3 * radius / (N : ℝ) < scale := by
      calc
        2 * Real.sqrt 3 * radius / (N : ℝ) <
            ((N : ℝ) * scale) / (N : ℝ) := by gcongr
        _ = scale := by field_simp [hNreal.ne']
    have heq : Real.sqrt 3 * (2 * radius / N) =
        2 * Real.sqrt 3 * radius / (N : ℝ) := by ring
    rw [heq]
    exact hdiv.le
  let normal (c : Cell) : Point3 :=
    let cross := wz1Cross (firstDirection c) (secondDirection c)
    (‖cross‖)⁻¹ • cross
  choose plusCover hplusCover using fun c : Cell =>
    grid_covering_cover (normal c) radius scale hradius N hN hscale hdiam
  choose minusCover hminusCover using fun c : Cell =>
    grid_covering_cover (-normal c) radius scale hradius N hN hscale hdiam
  let GridIndex := Fin 3 → Fin N
  let Label := Fin 2 × GridIndex
  let defaultLabel : Label := (0, fun _ => ⟨0, by omega⟩)
  let Near (p : Point3) (idx : Label) : Prop :=
    if idx.1 = 0 then
      dist (planeMap p) (normal (cell p)) ≤ radius ∧
        planeMap p ∈ plusCover (cell p) idx.2
    else
      ¬dist (planeMap p) (normal (cell p)) ≤ radius ∧
        planeMap p ∈ minusCover (cell p) idx.2
  have hcoverPreimagePlus : ∀ k : GridIndex,
      MeasurableSet {p : Point3 | planeMap p ∈ plusCover (cell p) k} := by
    intro k
    have heq : {p : Point3 | planeMap p ∈ plusCover (cell p) k} =
        ⋃ c : Cell, {p | cell p = c} ∩ planeMap ⁻¹' plusCover c k := by
      ext p
      simp
    rw [heq]
    apply MeasurableSet.iUnion
    intro c
    exact (hcell (measurableSet_singleton c)).inter
      ((hplusCover c).1 k |>.preimage hplaneMap)
  have hcoverPreimageMinus : ∀ k : GridIndex,
      MeasurableSet {p : Point3 | planeMap p ∈ minusCover (cell p) k} := by
    intro k
    have heq : {p : Point3 | planeMap p ∈ minusCover (cell p) k} =
        ⋃ c : Cell, {p | cell p = c} ∩ planeMap ⁻¹' minusCover c k := by
      ext p
      simp
    rw [heq]
    apply MeasurableSet.iUnion
    intro c
    exact (hcell (measurableSet_singleton c)).inter
      ((hminusCover c).1 k |>.preimage hplaneMap)
  have hnormalMeasurable : Measurable normal := Measurable.of_discrete
  have hdistanceMeasurable : Measurable fun p : Point3 =>
      dist (planeMap p) (normal (cell p)) := by
    fun_prop
  have hNearMeasurable : ∀ idx : Label, MeasurableSet {p | Near p idx} := by
    intro idx
    by_cases hside : idx.1 = 0
    · simp only [Near, if_pos hside, Set.setOf_and]
      exact (measurableSet_le hdistanceMeasurable measurable_const).inter
        (hcoverPreimagePlus idx.2)
    · simp only [Near, if_neg hside, Set.setOf_and]
      exact (measurableSet_le hdistanceMeasurable measurable_const).compl.inter
        (hcoverPreimageMinus idx.2)
  have hSMeasurable : MeasurableSet S.union := by
    have heq : S.union = ⋃ i : Fin F.card, S.carrier i := by
      ext p
      constructor
      · intro hp
        rcases hp with ⟨i, hi⟩
        exact Set.mem_iUnion.mpr ⟨i, hi⟩
      · intro hp
        rcases Set.mem_iUnion.mp hp with ⟨i, hi⟩
        exact ⟨i, hi⟩
    rw [heq]
    exact MeasurableSet.iUnion fun i => S.measurable_carrier i
  let P (p : Point3) (idx : Label) : Prop :=
    (p ∈ S.union ∧ Near p idx) ∨ (p ∉ S.union ∧ idx = defaultLabel)
  have hPMeasurable : ∀ idx : Label, MeasurableSet {p | P p idx} := by
    intro idx
    by_cases hdefault : idx = defaultLabel
    · have heq : {p : Point3 | P p idx} =
          (S.union ∩ {p | Near p idx}) ∪ S.unionᶜ := by
        ext p
        simp [P, hdefault]
      rw [heq]
      exact (hSMeasurable.inter (hNearMeasurable idx)).union hSMeasurable.compl
    · have heq : {p : Point3 | P p idx} =
          S.union ∩ {p | Near p idx} := by
        ext p
        simp [P, hdefault]
      rw [heq]
      exact hSMeasurable.inter (hNearMeasurable idx)
  have hPNonempty : ∀ p : Point3, ∃ idx : Label, P p idx := by
    intro p
    by_cases hp : p ∈ S.union
    · have hc : cell p ∈ activeCells := hsupport p hp
      have hnormalUnit : ‖normal (cell p)‖ = 1 := by
        have hcrossPos :
            0 < ‖wz1Cross (firstDirection (cell p))
              (secondDirection (cell p))‖ :=
          hkappa.trans_le (htransverse (cell p) hc)
        simp only [normal]
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hcrossPos]
        field_simp [hcrossPos.ne']
      have hfirst :
          |inner ℝ (planeMap p) (firstDirection (cell p))| ≤ incidence :=
        hfirstIncidence p hp
      have hsecond :
          |inner ℝ (planeMap p) (secondDirection (cell p))| ≤ incidence :=
        hsecondIncidence p hp
      rcases wz1_plane_projection_perturbation
          (firstDirection (cell p)) (secondDirection (cell p)) (planeMap p)
          (hfirstUnit (cell p)) (hsecondUnit (cell p)) (hplaneUnit p hp)
          kappa incidence hkappa hincidence (htransverse (cell p) hc)
          hfirst hsecond with ⟨sign, hsign, hclose⟩
      have hclose' :
          ‖planeMap p - sign • normal (cell p)‖ ≤ radius := by
        exact hclose
      by_cases hplus : dist (planeMap p) (normal (cell p)) ≤ radius
      · rcases (hplusCover (cell p)).2.1 (planeMap p) hplus with ⟨k, hk⟩
        refine ⟨(0, k), Or.inl ⟨hp, ?_⟩⟩
        exact ⟨hplus, hk⟩
      · have hsignMinus : sign = -1 := by
          rcases hsign with hsignPlus | hsignMinus
          · exfalso
            rw [hsignPlus] at hclose'
            simp only [one_smul] at hclose'
            exact hplus (by simpa [dist_eq_norm] using hclose')
          · exact hsignMinus
        have hminus : dist (planeMap p) (-normal (cell p)) ≤ radius := by
          rw [hsignMinus] at hclose'
          simpa [dist_eq_norm] using hclose'
        rcases (hminusCover (cell p)).2.1 (planeMap p) hminus with ⟨k, hk⟩
        refine ⟨(1, k), Or.inl ⟨hp, ?_⟩⟩
        exact ⟨hplus, hk⟩
    · exact ⟨defaultLabel, Or.inr ⟨hp, rfl⟩⟩
  let pairEquiv : Label ≃ Fin (Fintype.card Label) := Fintype.equivFin Label
  let labelLinearOrder : LinearOrder Label := Equiv.linearOrder pairEquiv
  letI : LinearOrder Label := labelLinearOrder
  rcases measurableFiniteChoice hPMeasurable hPNonempty with
    ⟨label, hlabelMeasurable, hlabelSpec, hlabelMinimal⟩
  have hlabelNear : ∀ p ∈ S.union, Near p (label p) := by
    intro p hp
    rcases hlabelSpec p with h | h
    · exact h.2
    · exact False.elim (h.1 hp)
  have hlabelFine : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      label first = label second := by
    intro first second hgrid
    have hcellEq : cell first = cell second := hcellFine first second hgrid
    have hplaneEq : planeMap first = planeMap second :=
      hplaneFine first second hgrid
    have hcarrier : ∀ index, first ∈ S.carrier index ↔
        second ∈ S.carrier index := by
      intro index
      exact hSCubical.carrier_mem_iff_of_same_cell index hgrid
    have hunion : first ∈ S.union ↔ second ∈ S.union := by
      constructor
      · rintro ⟨index, hindex⟩
        exact ⟨index, (hcarrier index).mp hindex⟩
      · rintro ⟨index, hindex⟩
        exact ⟨index, (hcarrier index).mpr hindex⟩
    have hnear : ∀ candidate, Near first candidate ↔ Near second candidate := by
      intro candidate
      simp only [Near]
      rw [hcellEq, hplaneEq]
    have hPiff : ∀ candidate, P first candidate ↔ P second candidate := by
      intro candidate
      simp only [P]
      rw [hunion, hnear candidate]
    have hforward := hlabelMinimal first (label second)
      ((hPiff (label second)).mpr (hlabelSpec second))
    have hbackward := hlabelMinimal second (label first)
      ((hPiff (label first)).mp (hlabelSpec first))
    exact @le_antisymm Label labelLinearOrder.toPartialOrder
      (label first) (label second) hforward hbackward
  have hsameLabel : ∀ p ∈ S.union, ∀ q ∈ S.union,
      cell p = cell q → label p = label q →
        dist (planeMap p) (planeMap q) ≤ scale := by
    intro p hp q hq hcellEq hlabelEq
    have hpNear := hlabelNear p hp
    have hqNear := hlabelNear q hq
    by_cases hside : (label p).1 = 0
    · have hpNear' :
          dist (planeMap p) (normal (cell p)) ≤ radius ∧
            planeMap p ∈ plusCover (cell p) (label p).2 := by
        simpa only [Near, if_pos hside] using hpNear
      have hpPlus : planeMap p ∈ plusCover (cell p) (label p).2 := hpNear'.2
      have hqPlus : planeMap q ∈ plusCover (cell p) (label p).2 := by
        rw [← hlabelEq] at hqNear
        have hqNear' :
            dist (planeMap q) (normal (cell q)) ≤ radius ∧
              planeMap q ∈ plusCover (cell q) (label p).2 := by
          simpa only [Near, if_pos hside] using hqNear
        simpa only [hcellEq] using hqNear'.2
      exact (hplusCover (cell p)).2.2 (label p).2
        (planeMap p) (planeMap q) hpPlus hqPlus
    · have hpNear' :
          ¬dist (planeMap p) (normal (cell p)) ≤ radius ∧
            planeMap p ∈ minusCover (cell p) (label p).2 := by
        simpa only [Near, if_neg hside] using hpNear
      have hpMinus : planeMap p ∈ minusCover (cell p) (label p).2 := hpNear'.2
      have hqMinus : planeMap q ∈ minusCover (cell p) (label p).2 := by
        rw [← hlabelEq] at hqNear
        have hqNear' :
            ¬dist (planeMap q) (normal (cell q)) ≤ radius ∧
              planeMap q ∈ minusCover (cell q) (label p).2 := by
          simpa only [Near, if_neg hside] using hqNear
        simpa only [hcellEq] using hqNear'.2
      exact (hminusCover (cell p)).2.2 (label p).2
        (planeMap p) (planeMap q) hpMinus hqMinus
  have hlabelCount : Fintype.card Label =
      wz1OrientationCapCount radius scale := by
    simp [Label, GridIndex, N, wz1OrientationCapCount, radius,
      Fintype.card_prod, Fintype.card_fun]
  have hallowedNonempty : ∀ _c ∈ activeCells,
      (Finset.univ : Finset Label).Nonempty := by
    intro _ _
    exact Finset.univ_nonempty
  have hlabelAllowed : ∀ p ∈ S.union,
      label p ∈ (Finset.univ : Finset Label) := by simp
  have hlabelBound : ∀ _c ∈ activeCells,
      ((Finset.univ : Finset Label).card : ENNReal) ≤
        (wz1OrientationCapCount radius scale : ENNReal) := by
    intro _ _
    rw [Finset.card_univ, hlabelCount]
  have hchosenMeasurable : ∀ chosen : Cell → Label, Measurable chosen :=
    fun _ => Measurable.of_discrete
  rcases paper_cellwise_bounded_label_variation_refinement
      S planeMap cell hcell activeCells hsupport label hlabelMeasurable
      (fun _ => Finset.univ) hallowedNonempty hlabelAllowed
      (wz1OrientationCapCount radius scale : ENNReal) hlabelBound
      hchosenMeasurable hsameLabel with
    ⟨chosenLabel, selected, hselectedEq, hselectedSub,
      hselectedVariation, hselectedMultiplicity, hselectedMass⟩
  have hselectedCubical : WZ1PaperIsCubicalShading selected := by
    rw [hselectedEq]
    exact paperCellwiseLabelRestriction_cubical hSCubical
      cell hcell label hlabelMeasurable chosenLabel
      (hchosenMeasurable chosenLabel) hcellFine hlabelFine
  exact ⟨selected, hselectedSub, hselectedCubical, hselectedVariation,
    hselectedMultiplicity, by simpa only [radius] using hselectedMass⟩

end Kakeya.Assouad

end
