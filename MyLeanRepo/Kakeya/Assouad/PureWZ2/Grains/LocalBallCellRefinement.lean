import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CellwiseFiniteLabelMassRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.GridCovering
import MyLeanRepo.Kakeya.Assouad.WZ1.MeasurableFiniteChoice

/-!
# Local plane-map cap refinement in each spatial cell

If all plane-map values in one spatial cell lie in a ball of radius R,
only that local ball needs to be covered. This is the quantitative refinement
used by the dense branch; its cost depends on R / scale, not on the inverse
of the target scale alone.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Number of coordinate caps needed to cover one local ball. -/
def localPlaneMapCapCount (radius scale : ℝ) : ℕ :=
  (Nat.ceil (2 * Real.sqrt 3 * radius / scale) + 1) ^ 3

/-- Refine independently in each spatial cell to one cap in a prescribed
local ball. The supplied plane-map function is unchanged. -/
theorem paper_local_ball_cell_refinement
    {delta radius scale : ℝ}
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
    (hsupport : ∀ point ∈ S.union, cell point ∈ activeCells)
    (center : Cell → Point3)
    (hradius : 0 ≤ radius) (hscale : 0 < scale)
    (hlocal : ∀ point ∈ S.union,
      dist (planeMap point) (center (cell point)) ≤ radius) :
    ∃ selected : WZ1PaperTubeShading F,
      PaperIsSubshading selected S ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ first ∈ selected.union, ∀ second ∈ selected.union,
        cell first = cell second →
          dist (planeMap first) (planeMap second) ≤ scale) ∧
      (∀ point ∈ selected.union,
        selected.pointMultiplicity point = S.pointMultiplicity point) ∧
      S.mass ≤
        (localPlaneMapCapCount radius scale : ENNReal) * selected.mass := by
  classical
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
  choose cap hcap using fun currentCell : Cell =>
    grid_covering_cover (center currentCell) radius scale
      hradius N hN hscale hdiam
  let Label := Fin 3 → Fin N
  let defaultLabel : Label := fun _ => ⟨0, by omega⟩
  have hcoverPreimage : ∀ label : Label,
      MeasurableSet {point : Point3 |
        planeMap point ∈ cap (cell point) label} := by
    intro label
    have heq : {point : Point3 |
        planeMap point ∈ cap (cell point) label} =
        ⋃ currentCell : Cell,
          {point | cell point = currentCell} ∩
            planeMap ⁻¹' cap currentCell label := by
      ext point
      simp
    rw [heq]
    apply MeasurableSet.iUnion
    intro currentCell
    exact (hcell (measurableSet_singleton currentCell)).inter
      (((hcap currentCell).1 label).preimage hplaneMap)
  have hSMeasurable : MeasurableSet S.union :=
    measurableSet_shading_union S
  let P (point : Point3) (label : Label) : Prop :=
    (point ∈ S.union ∧ planeMap point ∈ cap (cell point) label) ∨
      (point ∉ S.union ∧ label = defaultLabel)
  have hPMeasurable : ∀ label : Label,
      MeasurableSet {point | P point label} := by
    intro label
    by_cases hdefault : label = defaultLabel
    · have heq : {point : Point3 | P point label} =
          (S.union ∩ {point |
            planeMap point ∈ cap (cell point) label}) ∪ S.unionᶜ := by
        ext point
        simp [P, hdefault]
      rw [heq]
      exact (hSMeasurable.inter (hcoverPreimage label)).union
        hSMeasurable.compl
    · have heq : {point : Point3 | P point label} =
          S.union ∩ {point |
            planeMap point ∈ cap (cell point) label} := by
        ext point
        simp [P, hdefault]
      rw [heq]
      exact hSMeasurable.inter (hcoverPreimage label)
  have hPNonempty : ∀ point, ∃ label : Label, P point label := by
    intro point
    by_cases hpoint : point ∈ S.union
    · rcases (hcap (cell point)).2.1
          (planeMap point) (hlocal point hpoint) with
        ⟨label, hlabel⟩
      exact ⟨label, Or.inl ⟨hpoint, hlabel⟩⟩
    · exact ⟨defaultLabel, Or.inr ⟨hpoint, rfl⟩⟩
  let labelOrder : Label ≃ Fin (Fintype.card Label) :=
    Fintype.equivFin Label
  let labelLinearOrder : LinearOrder Label :=
    Equiv.linearOrder labelOrder
  letI : LinearOrder Label := labelLinearOrder
  rcases measurableFiniteChoice hPMeasurable hPNonempty with
    ⟨label, hlabelMeasurable, hlabelSpec, hlabelMinimal⟩
  have hlabelCap : ∀ point ∈ S.union,
      planeMap point ∈ cap (cell point) (label point) := by
    intro point hpoint
    rcases hlabelSpec point with hgood | hdefault
    · exact hgood.2
    · exact False.elim (hdefault.1 hpoint)
  have hlabelFine : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      label first = label second := by
    intro first second hgrid
    have hcellEq : cell first = cell second :=
      hcellFine first second hgrid
    have hplaneEq : planeMap first = planeMap second :=
      hplaneFine first second hgrid
    have hcarrier : ∀ index,
        first ∈ S.carrier index ↔ second ∈ S.carrier index := by
      intro index
      exact hSCubical.carrier_mem_iff_of_same_cell index hgrid
    have hunion : first ∈ S.union ↔ second ∈ S.union := by
      constructor
      · rintro ⟨index, hindex⟩
        exact ⟨index, (hcarrier index).mp hindex⟩
      · rintro ⟨index, hindex⟩
        exact ⟨index, (hcarrier index).mpr hindex⟩
    have hPiff : ∀ candidate,
        P first candidate ↔ P second candidate := by
      intro candidate
      simp only [P]
      rw [hunion, hcellEq, hplaneEq]
    have hforward := hlabelMinimal first (label second)
      ((hPiff (label second)).mpr (hlabelSpec second))
    have hbackward := hlabelMinimal second (label first)
      ((hPiff (label first)).mp (hlabelSpec first))
    exact @le_antisymm Label labelLinearOrder.toPartialOrder
      (label first) (label second) hforward hbackward
  have hsameLabel : ∀ first ∈ S.union, ∀ second ∈ S.union,
      cell first = cell second → label first = label second →
        dist (planeMap first) (planeMap second) ≤ scale := by
    intro first hfirst second hsecond hcellEq hlabelEq
    have hfirstCap := hlabelCap first hfirst
    have hsecondCap :
        planeMap second ∈ cap (cell first) (label first) := by
      simpa [hcellEq, hlabelEq] using hlabelCap second hsecond
    exact (hcap (cell first)).2.2 (label first)
      (planeMap first) (planeMap second) hfirstCap hsecondCap
  have hallowedNonempty : ∀ _ ∈ activeCells,
      (Finset.univ : Finset Label).Nonempty := by
    intro _ _
    exact Finset.univ_nonempty
  have hlabelAllowed : ∀ point ∈ S.union,
      label point ∈ (Finset.univ : Finset Label) := by simp
  have hlabelBound : ∀ _ ∈ activeCells,
      ((Finset.univ : Finset Label).card : ENNReal) ≤
        (localPlaneMapCapCount radius scale : ENNReal) := by
    intro _ _
    simp [localPlaneMapCapCount, Label, N, Fintype.card_fun]
  have hchosenMeasurable : ∀ chosen : Cell → Label, Measurable chosen :=
    fun _ => Measurable.of_discrete
  rcases paper_cellwise_bounded_label_variation_refinement
      S planeMap cell hcell activeCells hsupport label hlabelMeasurable
      (fun _ => Finset.univ) hallowedNonempty hlabelAllowed
      (localPlaneMapCapCount radius scale : ENNReal) hlabelBound
      hchosenMeasurable hsameLabel with
    ⟨chosenLabel, selected, hselectedEq, hselectedSub,
      hselectedVariation, hselectedMultiplicity, hselectedMass⟩
  have hselectedCubical : WZ1PaperIsCubicalShading selected := by
    rw [hselectedEq]
    exact paperCellwiseLabelRestriction_cubical hSCubical
      cell hcell label hlabelMeasurable chosenLabel
      (hchosenMeasurable chosenLabel) hcellFine hlabelFine
  exact ⟨selected, hselectedSub, hselectedCubical, hselectedVariation,
    hselectedMultiplicity, hselectedMass⟩

end Kakeya.Assouad.PureWZ2

end
