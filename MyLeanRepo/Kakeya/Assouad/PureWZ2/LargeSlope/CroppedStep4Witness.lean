import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CroppedRefinementData
import MyLeanRepo.Kakeya.Assouad.LargeSlope.XZGridIncidenceStatement
import MyLeanRepo.Kakeya.Assouad.LargeSlope.ProjectedNormalSliceStatement
import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.Statements

/-!
# Cropped Step 4 witness for pure WZ2 large-slope

Adapts `LargeSlopeStep4Witness` and its producer to the pure cropped-carrier
interface: no `UniformTubeStructure`, uses `WZ1PaperTubeShading` and
`PureWZ2LocalGrainData` instead of `C2GrainStructure`.

The witness structure is a paper-shading variant of the old one.
The producer is left as `sorry` pending the cropped refinement producer
(Steps 1–3) and the prism-cover adaptation.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/-- A translated `W × 4W × W` grid box, with `W = b - a`. -/
def xyzGridPrism
    (x₀ y₀ a b : ℝ) (index : ℤ × ℤ) : Set Point3 :=
  let W := b - a
  {p |
    p (0 : Fin 3) ∈
        Set.Ico (x₀ + (index.1 : ℝ) * W)
          (x₀ + ((index.1 : ℝ) + 1) * W) ∧
      p (1 : Fin 3) ∈
        Set.Ico (y₀ + (index.2 : ℝ) * (4 * W))
          (y₀ + ((index.2 : ℝ) + 1) * (4 * W)) ∧
      p (2 : Fin 3) ∈ Set.Icc a b}

/-- Per-tube fullness inside a slab for a paper tube shading. -/
def paperHasPerTubeMassInSlab {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading F) (a b : ℝ) (threshold : ENNReal) : Prop :=
  ∀ i, Y.carrier i ∩ horizontalSlab a b = ∅ ∨
    threshold ≤ MeasureTheory.volume (Y.carrier i ∩ horizontalSlab a b)

/--
The geometric Step 4 witness for the pure cropped-carrier setting.

Identical to `LargeSlopeStep4Witness` except `fine` is a paper shading
and the subshading relation is pointwise on carriers.

The absolute `total_piece_mass` bound was removed because it is only
needed for a trivial family-nonempty proof, which is supplied by
`cfg.extremal.nonempty` instead.
-/
structure LargeSlopeCroppedStep4Witness
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading F)
    (sigma eta a b : ℝ) where
  rho : ℝ
  rho_eq : rho = 64 * (b - a) ^ 2
  rho_pos : 0 < rho
  delta_le_rho : delta ≤ rho
  six_delta_le_rho : 6 * delta ≤ rho
  rho_le_quarter : rho ≤ 1 / 4
  sqrt_rho_eq : Real.sqrt rho = 8 * (b - a)
  fine : WZ1PaperTubeShading F
  fine_subshading : ∀ i, fine.carrier i ⊆ Y.carrier i
  fine_in_slab : ∀ i, fine.carrier i ⊆ horizontalSlab a b
  per_tube_full :
    paperHasPerTubeMassInSlab fine a b
      (ENNReal.ofReal
        (Real.rpow delta (11 * eta) * delta ^ 2 * Real.sqrt rho))
  prismCount : ℕ
  prismCount_pos : 0 < prismCount
  prism : Fin prismCount → Set Point3
  pieceCenter : Fin F.card → Fin prismCount → Point3
  pieceNormal : Fin F.card → Fin prismCount → Point3
  pieceNormal_unit : ∀ i j, ‖pieceNormal i j‖ = 1
  pieceNormal_lipschitz : ∀ (i i' : Fin F.card) (j : Fin prismCount),
      ‖pieceNormal i j - pieceNormal i' j‖ ≤ ‖pieceCenter i j - pieceCenter i' j‖
  -- Shared per-prism normal for convex overload
  prismNormal : Fin prismCount → Point3
  prismNormal_unit : ∀ j, ‖prismNormal j‖ = 1
  prismCenter : Fin prismCount → Point3
  prismCenter_in_prism : ∀ j, prismCenter j ∈ prism j
  prism_transverse :
    ∀ j, prism j ⊆
      {p | |inner ℝ (p - prismCenter j) (prismNormal j)| ≤ Real.sqrt rho}
  segmentStart : Fin F.card → Fin prismCount → ℝ
  piece : Fin F.card → Fin prismCount → Set Point3
  piece_measurable : ∀ i j, MeasurableSet (piece i j)
  piece_sub_fine : ∀ i j, piece i j ⊆ fine.carrier i
  piece_sub_prism : ∀ i j, piece i j ⊆ prism j
  piece_transverse :
    ∀ i j, piece i j ⊆
      {p | |inner ℝ (p - pieceCenter i j) (pieceNormal i j)| ≤ Real.sqrt rho}
  piece_sub_segment :
    ∀ i j, piece i j ⊆
      tubeSegmentCarrier (6 * delta) (F.tube i).base (F.tube i).direction
        (segmentStart i j) rho
  total_piece_mass_slab :
    (1 / 4 : ENNReal) * paperShadedMassInSlab Y a b ≤
      ∑ i : Fin F.card, ∑ j : Fin prismCount,
        MeasureTheory.volume (piece i j)
  piece_mass_lower :
    ∀ i j, MeasureTheory.volume (piece i j) ≠ 0 →
      ENNReal.ofReal
          (36 * Real.rpow delta (12 * eta) * delta ^ 2 *
            Real.sqrt rho) ≤
        MeasureTheory.volume (piece i j)
  piece_mass_upper :
    ∀ i j,
      MeasureTheory.volume (piece i j) ≤
        ENNReal.ofReal (36 * Real.sqrt rho * delta ^ 2)
  piece_local_ad :
    ∀ i j, MeasureTheory.volume (piece i j) ≠ 0 →
      IsADSet1
        (scalarProjection (prismNormal j) (piece i j))
        rho (1 - sigma)
        (Kakeya.realRpowENN delta (-(12 * eta)))
  prism_card_upper :
    (prismCount : ENNReal) ≤
      Kakeya.realRpowENN delta (-(12 * eta)) *
        Kakeya.realRpowENN rho ((-1 + sigma) / 2)
  pieceCenter_in_prism_slab :
    ∀ i j, pieceCenter i j ∈ prism j ∩ horizontalSlab a b

/--
Cropped version of `LargeSlopeStep4PrismCoverData`: no `UniformTubeStructure`.
Uses `LargeSlopeCroppedRefinementData` and paper shading.
-/
structure LargeSlopeCroppedStep4PrismCoverData
    {sigma loss delta : ℝ}
    {eta : ℝ} {C : ENNReal} {a b : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma loss delta}
    (refined : LargeSlopeCroppedRefinementData cfg eta C a b)
    (rho : ℝ)
    (fine : WZ1PaperTubeShading cfg.family) where
  prismCount : ℕ
  prismCount_pos : 0 < prismCount
  gridOriginX : ℝ
  gridOriginY : ℝ
  gridIndex : Fin prismCount → ℤ × ℤ
  gridIndex_injective : Function.Injective gridIndex
  sourcePoint : Fin prismCount → Point3
  sourcePoint_mem : ∀ j, sourcePoint j ∈ fine.union
  fine_subshading : ∀ i, fine.carrier i ⊆ refined.shading.carrier i
  sourcePoint_grid :
    ∀ j, sourcePoint j ∈
      xyzGridPrism gridOriginX gridOriginY a b (gridIndex j)
  prism : Fin prismCount → Set Point3
  prism_eq_grid :
    ∀ j, prism j =
      xyzGridPrism gridOriginX gridOriginY a b (gridIndex j)
  pieceCenter : Fin cfg.family.card → Fin prismCount → Point3
  pieceNormal : Fin cfg.family.card → Fin prismCount → Point3
  pieceNormal_unit : ∀ i j, ‖pieceNormal i j‖ = 1
  pieceNormal_lipschitz : ∀ (i i' : Fin cfg.family.card) (j : Fin prismCount),
      ‖pieceNormal i j - pieceNormal i' j‖ ≤ ‖pieceCenter i j - pieceCenter i' j‖
  -- Shared per-prism normal for convex overload
  prismNormal : Fin prismCount → Point3
  prismNormal_unit : ∀ j, ‖prismNormal j‖ = 1
  prism_transverse :
    ∀ j, prism j ⊆
      {p | |inner ℝ (p - sourcePoint j) (prismNormal j)| ≤ Real.sqrt rho}
  pieceCenter_in_prism_slab :
    ∀ i j, pieceCenter i j ∈ prism j ∩ horizontalSlab a b
  segmentStart : Fin cfg.family.card → Fin prismCount → ℝ
  piece : Fin cfg.family.card → Fin prismCount → Set Point3
  piece_measurable : ∀ i j, MeasurableSet (piece i j)
  piece_eq : ∀ i j, piece i j = fine.carrier i ∩ prism j
  piece_sub_fine : ∀ i j, piece i j ⊆ fine.carrier i
  piece_sub_prism : ∀ i j, piece i j ⊆ prism j
  piece_transverse :
    ∀ i j, piece i j ⊆
      {p | |inner ℝ (p - pieceCenter i j) (pieceNormal i j)| ≤ Real.sqrt rho}
  piece_sub_segment :
    ∀ i j, piece i j ⊆
      tubeSegmentCarrier (6 * delta)
        (cfg.family.tube i).base
        (cfg.family.tube i).direction
        (segmentStart i j) rho
  support : Fin cfg.family.card → Finset (Fin prismCount)
  support_card : ∀ i, (support i).card ≤ 16
  mem_support_iff :
    ∀ i j, j ∈ support i ↔ MeasureTheory.volume (piece i j) ≠ 0
  covers_fine :
    ∀ i p, p ∈ fine.carrier i →
      ∃ j : Fin prismCount, p ∈ piece i j
  piece_mass_upper :
    ∀ i j,
      MeasureTheory.volume (piece i j) ≤
        ENNReal.ofReal (36 * Real.sqrt rho * delta ^ 2)
  piece_local_ad :
    ∀ i j, MeasureTheory.volume (piece i j) ≠ 0 →
      IsADSet1
        (scalarProjection (prismNormal j) (piece i j))
        rho (1 - sigma)
        (Kakeya.realRpowENN delta (-(12 * eta)))
  prism_card_upper :
    (prismCount : ENNReal) ≤
      Kakeya.realRpowENN delta (-(12 * eta)) *
        Kakeya.realRpowENN rho ((-1 + sigma) / 2)

/-- Cropped Step 4 witness producer statement. -/
def LargeSlopeCroppedStep4WitnessStatement : Prop :=
  ∀ epsilon sigma loss : ℝ,
    0 < epsilon → epsilon ≤ 1 / 2 →
    0 < sigma → sigma < 1 →
    0 < loss → loss ≤ epsilon →
    1000 * loss ≤ epsilon * sigma ^ 2 →
    ∃ eta delta₀ : ℝ,
      0 < eta ∧ eta ≤ epsilon ∧
      loss ≤ eta ∧
      epsilon * sigma ^ 2 / 2000 ≤ eta ∧
      1000 * eta ≤ epsilon * sigma ^ 2 ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ (cfg : PureWZ2C2GrainConfiguration sigma loss delta)
          (C : ENNReal) (a b : ℝ)
          (refined : LargeSlopeCroppedRefinementData cfg eta C a b),
          b - a ≤ Real.rpow delta epsilon →
          ∀ z ∈ Set.Icc a b,
            |deriv refined.globalGrains.slope z| < b - a →
            Nonempty
              (LargeSlopeCroppedStep4Witness
                refined.shading sigma eta a b)

end Kakeya.Assouad

end
