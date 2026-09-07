import MyLeanRepo.Kakeya.Assouad.PureWZ2.Critical
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12Output

/-!
# Pure WZ2 `prop: sticky`

This module freezes the complete self-similar decomposition in WZ2 Section 6.
The public structure is literal Definition 2.12.  Cropped WZ tubes and their
unique line-cover parent remain an internal certificate on the same selected
families.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
The literal dense-cell replacement described at the start of WZ2 Section 6.

The selected paper cell must lie in the cropped WZ tube and must contain at
least one hundredth of the source tube's average shaded proportion.  The
paper's displayed prose omits the dimensionally necessary factor `|Q|`; the
formula below is its only scale-consistent interpretation.
-/
def pureWZ2DenseCubicalization
    {delta : ℝ}
    (tube : Kakeya.DeltaTube delta)
    (source : Set Point3) : Set Point3 :=
  {point |
    let cell := wz1PaperGridIndex delta point
    wz1PaperGridCube delta cell ⊆
        wz1PaperTubeCarrier tube ∧
      (100 : ENNReal)⁻¹ *
          volume source *
          (volume tube.carrier)⁻¹ *
          volume (wz1PaperGridCube delta cell) ≤
        volume
          (source ∩ wz1PaperGridCube delta cell)}

/--
The complete Section 6 cover relation at the prescribed output scale.

No arbitrary parent is stored.  The fiber over `parent` is exactly the set of
all fine tubes covered by that parent in the WZ line metric.
-/
structure PureWZ2Section6Cover
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho) : Prop where
  fine_line_class : WZ1PaperIsLineClass fine
  coarse_line_class : WZ1PaperIsLineClass coarse
  covers :
    ∀ source : Fin fine.card,
      ∃ parent : Fin coarse.card,
        WZ1PaperTubeCovers
          (fine.tube source) (coarse.tube parent)
  parent_hit :
    ∀ parent : Fin coarse.card,
      ∃ source : Fin fine.card,
        WZ1PaperTubeCovers
          (fine.tube source) (coarse.tube parent)
  coarse_essentially_distinct :
    WZ1PaperIsEssentiallyDistinct coarse

/--
The paper's balanced-cover condition, synchronized with the public strict
full fibers.

The final field is the defining balance condition from the paragraph before
`prop: sticky`: every active coarse cube carries the same fine shaded mass.
-/
structure PureWZ2BalancedCoverData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (croppedCoarse : WZ1PaperTubeShading coarse) where
  point_compatibility :
    ∀ source parent,
      WZ1PaperTubeCovers
          (fine.tube source) (coarse.tube parent) →
        ∀ point,
          point ∈ fineShading.carrier source →
            point ∈ croppedCoarse.carrier parent
  coarse_cubical :
    WZ1PaperIsCubicalShading croppedCoarse
  activeCells : Finset (ℤ × ℤ × ℤ)
  coarse_union_eq :
    croppedCoarse.union =
      ⋃ cell ∈ activeCells,
        wz1PaperGridCube rho cell
  cellMass : ENNReal
  cellMass_pos : 0 < cellMass
  cellMass_ne_top : cellMass ≠ ⊤
  fine_cell_mass :
    ∀ cell ∈ activeCells,
      volume
          (fineShading.union ∩
            wz1PaperGridCube rho cell) =
        cellMass

namespace PureWZ2BalancedCoverData

variable {delta rho : ℝ} {fine : Kakeya.Streamlined.TubeFamily delta}
  {coarse : Kakeya.Streamlined.TubeFamily rho}
  {cover : PureWZ2Section6Cover fine coarse}
  {fineShading : WZ1PaperTubeShading fine}
  {croppedCoarse : WZ1PaperTubeShading coarse}
  (self : PureWZ2BalancedCoverData cover fineShading croppedCoarse)

/-- The intersection of the fine shading union with each active cell is nonempty
    because it has positive volume (`cellMass > 0`). -/
lemma cellIntersection_nonempty (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ self.activeCells) :
    (fineShading.union ∩ wz1PaperGridCube rho cell).Nonempty := by
  have hvol : volume (fineShading.union ∩ wz1PaperGridCube rho cell) = self.cellMass :=
    self.fine_cell_mass cell hcell
  by_contra h
  have h_empty : (fineShading.union ∩ wz1PaperGridCube rho cell) = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp h
  have h_zero : volume (fineShading.union ∩ wz1PaperGridCube rho cell) = 0 := by
    rw [h_empty]
    <;> exact MeasureTheory.measure_empty
  rw [h_zero] at hvol
  exact self.cellMass_pos.ne' hvol.symm

/-- A representative point in each active cell, chosen from the fine shading union. -/
noncomputable def cellRep (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ self.activeCells) : Point3 :=
  Classical.choose (self.cellIntersection_nonempty cell hcell)

lemma cellRep_in_union (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ self.activeCells) :
    self.cellRep cell hcell ∈ fineShading.union :=
  (Classical.choose_spec (self.cellIntersection_nonempty cell hcell)).1

lemma cellRep_in_cell (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ self.activeCells) :
    self.cellRep cell hcell ∈ wz1PaperGridCube rho cell :=
  (Classical.choose_spec (self.cellIntersection_nonempty cell hcell)).2

end PureWZ2BalancedCoverData

/-- The complete four-item output of the pure WZ2 `prop: sticky`. -/
structure PureWZ2PropStickyData
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : WZ1PaperTubeShading source)
    (rho : WZ2PaperRequestedScale delta)
    (logExponent : ℕ) where
  selected : Kakeya.Streamlined.TubeSubfamily source
  selected_nonempty : selected.family.Nonempty
  refined :
    WZ1PaperTubeShading selected.family
  subshading :
    ∀ index,
      refined.carrier index ⊆
        sourceShading.carrier (selected.embedding index)
  retained_mass :
    wz2PaperPureRefinementFraction delta logExponent *
        sourceShading.mass ≤
      refined.mass
  refined_cubical :
    WZ1PaperIsCubicalShading refined
  coarse : Kakeya.Streamlined.TubeFamily rho.1
  cover :
    PureWZ2Section6Cover selected.family coarse
  croppedCoarseShading :
    WZ1PaperTubeShading coarse
  balanced :
    PureWZ2BalancedCoverData
      cover refined croppedCoarseShading
  coarse_extremal :
    WZ2PaperCroppedIsExtremal
      sigma outputLoss coarse croppedCoarseShading
  rescaledFiber :
    ∀ parent : Fin coarse.card,
      Nonempty
        (WZ2PaperPureRescaledFullFiberOutput
          (sigma := sigma) (loss := outputLoss)
          (restrictPaperShading
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              selected.family
              (wz2PaperFullFiberIndices
                selected.family coarse parent))
            refined)
          (coarse.tube parent)
          coarse_extremal.delta_pos)
  coarse_multiplicity_upper :
    ∀ point,
      (croppedCoarseShading.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN rho.1
            (2 - sigma - outputLoss) *
          coarse.enncard
  fiber_multiplicity_upper :
    ∀ parent point,
      (((wz2PaperFullFiberIndices
          selected.family coarse parent).filter
          fun source =>
            point ∈ refined.carrier source).card :
          ENNReal) ≤
        Kakeya.realRpowENN (delta / rho.1)
            (2 - sigma - outputLoss) *
          ((wz2PaperFullFiberIndices
            selected.family coarse parent).card : ENNReal)

/--
One provenance-preserving ordinary-to-cropped normalization.

The ordinary source, selected subfamily, ordinary subshading, and cropped
shading are tied together in one dependent record.  In particular,
`cropped_carrier_eq_dense_cubicalization` is the formal content of the
paper's replacement of the shading by selected grid cubes; the output is not
an unrelated cropped extremizer.
-/
structure PureWZ2CroppedCriticalNormalizationData
    {sigma inputLoss outputLoss delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration
        sigma inputLoss delta)
    (logExponent : ℕ) where
  /-- The source loss is chosen before the fine scale with a fixed gap to the
  cropped output loss. -/
  input_loss_le_half : inputLoss ≤ outputLoss / 2
  selected : Kakeya.Streamlined.TubeSubfamily source.family
  selected_nonempty : selected.family.Nonempty
  ordinaryRefined :
    Kakeya.Streamlined.TubeShading selected.family
  ordinary_subshading :
    ∀ index,
      ordinaryRefined.carrier index ⊆
        source.shading.carrier (selected.embedding index)
  retained_mass :
    wz2PaperPureRefinementFraction delta logExponent *
        source.shading.mass ≤
      ordinaryRefined.mass
  frame : Point3 ≃ᵃⁱ[ℝ] Point3
  croppedFamily : Kakeya.Streamlined.TubeFamily delta
  indexEquiv :
    Fin selected.family.card ≃ Fin croppedFamily.card
  ordinary_carrier_image_eq :
    ∀ index,
      (croppedFamily.tube (indexEquiv index)).carrier =
        frame '' (selected.family.tube index).carrier
  /-- Each retained ordinary shading has quantitative density in its
  ordinary unit-segment carrier before applying the common rigid frame. -/
  ordinary_per_tube :
    ∀ index,
      (Kakeya.realRpowENN delta inputLoss / 2) *
            volume (selected.family.tube index).carrier ≤
        volume (ordinaryRefined.carrier index)
  /-- After applying the common frame, every retained ordinary shading lies
  in the central axial window used to compare finite ordinary tubes. -/
  ordinary_axial_window :
    ∀ index point,
      point ∈ frame '' ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 4
  croppedRefined : WZ1PaperTubeShading croppedFamily
  cropped_carrier_eq_dense_cubicalization :
    ∀ index,
      croppedRefined.carrier (indexEquiv index) =
        pureWZ2DenseCubicalization
          (croppedFamily.tube (indexEquiv index))
          (frame '' ordinaryRefined.carrier index)
  cropped_cubical :
    WZ1PaperIsCubicalShading croppedRefined
  line_class :
    WZ1PaperIsLineClass croppedFamily
  cropped_top_level_cwa :
    WZ2PaperConvexWolffBound
      croppedFamily
      (Kakeya.realRpowENN delta (-outputLoss))
  final_extremal :
    WZ2PaperCroppedIsExtremal
      sigma outputLoss
      croppedFamily croppedRefined
  /-- Every source-intersecting grid cell is a genuine cropped paper cell. -/
  ordinary_cell_containment :
    ∀ index (cell : ℤ × ℤ × ℤ),
      ((frame '' ordinaryRefined.carrier index) ∩
          wz1PaperGridCube delta cell).Nonempty →
        wz1PaperGridCube delta cell ⊆
          wz1PaperTubeCarrier
            (croppedFamily.tube (indexEquiv index))
  /-- The normalized ordinary representatives stay in the fixed analytic
  basepoint window. -/
  ordinary_bounded_base :
    HasBoundedBase croppedFamily 4

/--
Normalize arbitrarily small pure critical configurations into the cropped WZ
tube and cubical-shading convention used throughout Section 6, while retaining
the exact ordinary source and selected-subfamily provenance.
-/
def PureWZ2CroppedCriticalNormalizationAt
    (normalizationExponent : ℕ) : Prop :=
  ∀ sigma : ℝ,
    PureWZ2CriticalPackage sigma →
      ∀ outputLoss delta₀ : ℝ,
        0 < outputLoss → 0 < delta₀ →
          ∃ inputLoss delta : ℝ,
            0 < inputLoss ∧
            inputLoss ≤ outputLoss ∧
            0 < delta ∧ delta ≤ delta₀ ∧
            ∃ source :
                PureWZ2ExtremalConfiguration
                  sigma inputLoss delta,
              Nonempty
                (PureWZ2CroppedCriticalNormalizationData
                  (outputLoss := outputLoss)
                  source normalizationExponent)

/-- Existential public wrapper for the normalization leaf. -/
def PureWZ2CroppedCriticalNormalizationStatement : Prop :=
  ∃ normalizationExponent : ℕ,
    PureWZ2CroppedCriticalNormalizationAt normalizationExponent

/-- The universal cropped-model form of WZ2 `prop: sticky`. -/
def PureWZ2CroppedPropStickyAt
    (normalizationExponent logExponent : ℕ) : Prop :=
  ∀ sigma : ℝ,
    ∀ _critical : PureWZ2CriticalPackage sigma,
    ∀ outputLoss : ℝ, 0 < outputLoss →
      ∃ sourceLoss normalizationLoss delta₀ : ℝ,
        0 < sourceLoss ∧
        0 < normalizationLoss ∧
        sourceLoss ≤ normalizationLoss / 2 ∧
        normalizationLoss < outputLoss ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ source :
              PureWZ2ExtremalConfiguration
                sigma sourceLoss delta,
            ∀ normalized :
                PureWZ2CroppedCriticalNormalizationData
                  (outputLoss := normalizationLoss)
                  source normalizationExponent,
                ∀ rho : WZ2PaperRequestedScale delta,
                  Real.rpow delta (1 - outputLoss) ≤ rho.1 →
                  rho.1 ≤ Real.rpow delta outputLoss →
                    Nonempty
                      (PureWZ2PropStickyData
                        (sigma := sigma)
                        (outputLoss := outputLoss)
                        normalized.croppedRefined rho logExponent)

/-- Existential public wrapper for the universal cropped `prop: sticky`. -/
def PureWZ2CroppedPropStickyStatement : Prop :=
  ∃ normalizationExponent logExponent : ℕ,
    PureWZ2CroppedPropStickyAt
      normalizationExponent logExponent

/--
One genuinely composable realization of cropped normalization followed by
`prop: sticky`.  The source and normalized configuration are shared dependent
witnesses, rather than independent existential choices hidden behind two
universal statements.
-/
structure PureWZ2PropStickyRealizationData
    {sigma outputLoss scaleCeiling : ℝ}
    (normalizationExponent logExponent : ℕ) where
  continuationLoss : ℝ
  sourceLoss : ℝ
  normalizationLoss : ℝ
  delta : ℝ
  continuationLoss_pos : 0 < continuationLoss
  continuationLoss_lt_output : continuationLoss < outputLoss
  continuationLoss_le_half : continuationLoss ≤ 1 / 2
  sourceLoss_pos : 0 < sourceLoss
  normalizationLoss_pos : 0 < normalizationLoss
  sourceLoss_le_half : sourceLoss ≤ normalizationLoss / 2
  normalizationLoss_lt_continuation :
    normalizationLoss < continuationLoss
  delta_pos : 0 < delta
  delta_le_ceiling : delta ≤ scaleCeiling
  source :
    PureWZ2ExtremalConfiguration sigma sourceLoss delta
  normalized :
    PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss)
      source normalizationExponent
  normalized_ordinary_axial_window_eighth :
    ∀ index point,
      point ∈
          normalized.frame ''
            normalized.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8
  output :
    ∀ rho : WZ2PaperRequestedScale delta,
      Real.rpow delta (1 - continuationLoss) ≤ rho.1 →
      rho.1 ≤ Real.rpow delta continuationLoss →
        Nonempty
          (PureWZ2PropStickyData
            (sigma := sigma)
            (outputLoss := outputLoss)
            normalized.croppedRefined rho logExponent)
  realizedRho : WZ2PaperRequestedScale delta
  realizedRho_eq_sqrt :
    realizedRho.1 = Real.sqrt delta
  realizedRho_lower :
    Real.rpow delta (1 - continuationLoss) ≤ realizedRho.1
  realizedRho_upper :
    realizedRho.1 ≤ Real.rpow delta continuationLoss
  realizedOutput :
    Nonempty
      (PureWZ2PropStickyData
        (sigma := sigma)
        (outputLoss := outputLoss)
        normalized.croppedRefined realizedRho logExponent)

/--
At every requested smallness threshold, Node 3 realizes one compatible
ordinary source, cropped normalization, and nonvacuous Proposition 6.2 output.
-/
def PureWZ2PropStickyRealizationAt
    (normalizationExponent logExponent : ℕ) : Prop :=
  ∀ sigma : ℝ,
    PureWZ2CriticalPackage sigma →
      ∀ outputLoss scaleCeiling : ℝ,
        0 < outputLoss → 0 < scaleCeiling →
          Nonempty
            (PureWZ2PropStickyRealizationData
              (sigma := sigma)
              (outputLoss := outputLoss)
              (scaleCeiling := scaleCeiling)
              normalizationExponent logExponent)

/-- Node 3's complete mathematical output. -/
def PureWZ2PropStickyFromCriticalStatement : Prop :=
  ∃ normalizationExponent logExponent : ℕ,
    PureWZ2CroppedCriticalNormalizationAt normalizationExponent ∧
      PureWZ2CroppedPropStickyAt
        normalizationExponent logExponent ∧
      PureWZ2PropStickyRealizationAt
        normalizationExponent logExponent

/--
Historical Node 3 interface retained only for generic assembly lemmas that do
not produce the public re-entry kernel.
-/
def PureWZ2PropStickyLegacyStatement : Prop :=
  PureWZ2SubunitPackageStatement →
    PureWZ2CriticalExtractionStatement →
      PureWZ2PropStickyFromCriticalStatement

end Kakeya.Assouad

end
