import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.BaseConfigWithSticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63InitialLocalGrainReentry

/-!
# Root normalization for Proposition 6.3

The first ordinary-trace re-entry needs one geometric fact which is absent
from the historical Node 3 normalization record: every grid cell meeting the
framed ordinary shading lies in the corresponding cropped paper carrier.
This file packages that fact and the synchronized per-tube ordinary density
alongside the frozen normalization, and preserves both through the loss
weakenings used to match Node 3's quantifier order.

No normalization is manufactured here.  The strengthened producer below is
the precise boundary which a provenance-correct Node 3 normalization must
satisfy.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory

/-- Canonical power weight for external trace regularization.  Its exponent
is chosen strictly between the ordinary-density/current-extremality losses
and the later re-entry loss, leaving room on both sides for fixed constants
and the nearby-CWA regularization cost. -/
def proposition63CanonicalReentryWeight
    (delta weightLoss : ℝ) : ENNReal :=
  Kakeya.realRpowENN delta (weightLoss + 2)

theorem proposition63CanonicalReentryWeight_ne_zero
    {delta weightLoss : ℝ}
    (delta_pos : 0 < delta) :
    proposition63CanonicalReentryWeight delta weightLoss ≠ 0 := by
  unfold proposition63CanonicalReentryWeight
  exact (ENNReal.ofReal_pos.mpr
    (Real.rpow_pos_of_pos delta_pos _)).ne'

theorem proposition63CanonicalReentryWeight_ne_top
    {delta weightLoss : ℝ} :
    proposition63CanonicalReentryWeight delta weightLoss ≠ ⊤ := by
  simp [proposition63CanonicalReentryWeight, Kakeya.realRpowENN]

theorem proposition63CanonicalReentryWeight_trace_scale
    {delta weightLoss reentryLoss : ℝ}
    (delta_pos : 0 < delta)
    (delta_le_one : delta ≤ 1) :
    (96 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta (reentryLoss - weightLoss) ≤ 1 →
    4 * (Kakeya.realRpowENN delta reentryLoss *
        Kakeya.deltaTubeVolume delta) ≤
      proposition63CanonicalReentryWeight delta weightLoss := by
  intro fixed_absorb
  have tubeVolumeUpper : Kakeya.deltaTubeVolume delta ≤
      24 * Kakeya.realRpowENN delta 2 *
        Kakeya.deltaTubeVolume 1 := by
    let family : Kakeya.Streamlined.TubeFamily delta :=
      { card := 1
        tube := fun _ =>
          { base := 0
            direction := EuclideanSpace.single (0 : Fin 3) 1
            direction_unit := by simp } }
    have upper := tube_volume_scaling.2.2 delta delta_pos delta_le_one
      (family.tube ⟨0, by norm_num⟩)
    rw [tube_volume_scaling.1 delta
      (family.tube ⟨0, by norm_num⟩)] at upper
    exact upper
  calc
    4 * (Kakeya.realRpowENN delta reentryLoss *
          Kakeya.deltaTubeVolume delta) ≤
        4 * (Kakeya.realRpowENN delta reentryLoss *
          (24 * Kakeya.realRpowENN delta 2 *
            Kakeya.deltaTubeVolume 1)) := by gcongr
    _ = (4 * 24 : ENNReal) * Kakeya.deltaTubeVolume 1 *
          (Kakeya.realRpowENN delta reentryLoss *
            Kakeya.realRpowENN delta 2) := by ring
    _ = (96 : ENNReal) * Kakeya.deltaTubeVolume 1 *
          Kakeya.realRpowENN delta (reentryLoss + 2) := by
      rw [realRpowENN_add delta_pos]
      ring
    _ = ((96 : ENNReal) * Kakeya.deltaTubeVolume 1 *
          Kakeya.realRpowENN delta (reentryLoss - weightLoss)) *
          Kakeya.realRpowENN delta (weightLoss + 2) := by
      have split :
          Kakeya.realRpowENN delta (reentryLoss - weightLoss) *
              Kakeya.realRpowENN delta (weightLoss + 2) =
            Kakeya.realRpowENN delta (reentryLoss + 2) := by
        have exponentEq :
            (reentryLoss - weightLoss) + (weightLoss + 2) =
              reentryLoss + 2 := by ring
        calc
          Kakeya.realRpowENN delta (reentryLoss - weightLoss) *
                Kakeya.realRpowENN delta (weightLoss + 2) =
              Kakeya.realRpowENN delta
                ((reentryLoss - weightLoss) + (weightLoss + 2)) :=
            (realRpowENN_add delta_pos _ _).symm
          _ = Kakeya.realRpowENN delta (reentryLoss + 2) :=
            congrArg (Kakeya.realRpowENN delta) exponentEq
      have expanded :
          (96 : ENNReal) * Kakeya.deltaTubeVolume 1 *
                Kakeya.realRpowENN delta (reentryLoss + 2) =
            ((96 : ENNReal) * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN delta (reentryLoss - weightLoss)) *
              Kakeya.realRpowENN delta (weightLoss + 2) := by
        have lifted := congrArg
          (fun value : ENNReal =>
            ((96 : ENNReal) * Kakeya.deltaTubeVolume 1) * value) split.symm
        simpa only [mul_assoc] using lifted
      exact expanded
    _ ≤ 1 * Kakeya.realRpowENN delta (weightLoss + 2) := by gcongr
    _ = proposition63CanonicalReentryWeight delta weightLoss := by
      simp [proposition63CanonicalReentryWeight]

theorem proposition63CanonicalReentryWeight_paper_scale
    {delta weightLoss reentryLoss : ℝ}
    (delta_pos : 0 < delta)
    (delta_small : delta ≤ 1 / 24)
    (fixed_absorb :
      ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta (reentryLoss - weightLoss) ≤
        (73 / 100 : ENNReal))
    {family : Kakeya.Streamlined.TubeFamily delta}
    (line_class : WZ1PaperIsLineClass family)
    (index : Fin family.card) :
    4 * (Kakeya.realRpowENN delta reentryLoss *
        volume (wz1PaperTubeCarrier (family.tube index))) ≤
      (73 / 100 : ENNReal) *
        proposition63CanonicalReentryWeight delta weightLoss := by
  have carrierVolumeUpper :=
    (wz2PaperTubeCarrier_convex_and_volume_quadratic
      wz2_paper_tube_carrier_geometry delta_pos delta_small
      (family.tube index) (line_class index)).2
  calc
    4 * (Kakeya.realRpowENN delta reentryLoss *
          volume (wz1PaperTubeCarrier (family.tube index))) ≤
        4 * (Kakeya.realRpowENN delta reentryLoss *
          ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2)) := by gcongr
    _ = 4 * (((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          (Kakeya.realRpowENN delta reentryLoss *
            Kakeya.realRpowENN delta 2)) := by ring
    _ = ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta (reentryLoss + 2) := by
      rw [realRpowENN_add delta_pos]
      ring
    _ = ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1 *
          Kakeya.realRpowENN delta (reentryLoss - weightLoss)) *
          Kakeya.realRpowENN delta (weightLoss + 2) := by
      have split :
          Kakeya.realRpowENN delta (reentryLoss - weightLoss) *
              Kakeya.realRpowENN delta (weightLoss + 2) =
            Kakeya.realRpowENN delta (reentryLoss + 2) := by
        have exponentEq :
            (reentryLoss - weightLoss) + (weightLoss + 2) =
              reentryLoss + 2 := by ring
        calc
          Kakeya.realRpowENN delta (reentryLoss - weightLoss) *
                Kakeya.realRpowENN delta (weightLoss + 2) =
              Kakeya.realRpowENN delta
                ((reentryLoss - weightLoss) + (weightLoss + 2)) :=
            (realRpowENN_add delta_pos _ _).symm
          _ = Kakeya.realRpowENN delta (reentryLoss + 2) :=
            congrArg (Kakeya.realRpowENN delta) exponentEq
      have expanded :
          ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
                Kakeya.realRpowENN delta (reentryLoss + 2) =
            (((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN delta (reentryLoss - weightLoss)) *
              Kakeya.realRpowENN delta (weightLoss + 2) := by
        have lifted := congrArg
          (fun value : ENNReal =>
            ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) * value)
          split.symm
        simpa only [mul_assoc] using lifted
      exact expanded
    _ ≤ (73 / 100 : ENNReal) *
        Kakeya.realRpowENN delta (weightLoss + 2) := by gcongr
    _ = (73 / 100 : ENNReal) *
        proposition63CanonicalReentryWeight delta weightLoss := by
      simp [proposition63CanonicalReentryWeight]

/-- The fixed geometric constants in the two lower weight bounds are absorbed
simultaneously below one scale threshold. -/
theorem exists_delta_proposition63CanonicalReentryWeight_scale_bounds
    {weightLoss reentryLoss : ℝ}
    (loss_gap : weightLoss < reentryLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        (96 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN delta (reentryLoss - weightLoss) ≤ 1 ∧
          ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN delta (reentryLoss - weightLoss) ≤
            (73 / 100 : ENNReal) := by
  let gap : ℝ := reentryLoss - weightLoss
  have gap_pos : 0 < gap := by
    dsimp only [gap]
    linarith
  let constant : ENNReal :=
    max (96 * Kakeya.deltaTubeVolume 1)
      (2 * ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1))
  have constant_ne_top : constant ≠ ⊤ := by
    apply max_ne_top
    · exact ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top
    · exact ENNReal.mul_ne_top (by norm_num)
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by norm_num) (by norm_num))
          deltaTubeVolume_one_ne_top)
  rcases exists_delta_realRpowENN_bound constant constant_ne_top gap_pos with
    ⟨delta₀, delta₀_pos, delta₀_le_one, bound⟩
  refine ⟨delta₀, delta₀_pos, delta₀_le_one, ?_⟩
  intro delta delta_pos delta_le
  have product_bound :
      constant * Kakeya.realRpowENN delta gap ≤ 1 := by
    calc
      constant * Kakeya.realRpowENN delta gap ≤
          Kakeya.realRpowENN delta (-gap) *
            Kakeya.realRpowENN delta gap := by
        gcongr
        exact bound delta delta_pos delta_le
      _ = Kakeya.realRpowENN delta ((-gap) + gap) := by
        rw [realRpowENN_add delta_pos]
      _ = 1 := by simp [Kakeya.realRpowENN]
  constructor
  · exact (mul_le_mul_right' (le_max_left _ _) _).trans product_bound
  · have doubled :
        2 * (((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta gap) ≤ 1 := by
      calc
        2 * (((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN delta gap) =
            (2 * ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1)) *
              Kakeya.realRpowENN delta gap := by ring
        _ ≤ constant * Kakeya.realRpowENN delta gap := by
          gcongr
          exact le_max_right _ _
        _ ≤ 1 := product_bound
    have half_bound_raw :=
      (ENNReal.mul_le_iff_le_inv (by norm_num) (by norm_num)).mp doubled
    have half_bound :
        ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN delta gap ≤ (2 : ENNReal)⁻¹ := by
      simpa only [mul_one] using half_bound_raw
    have half_le : (2 : ENNReal)⁻¹ ≤ (73 / 100 : ENNReal) := by
      apply (ENNReal.toReal_le_toReal
        (ENNReal.inv_ne_top.mpr (by norm_num))
        (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
      norm_num [ENNReal.toReal_inv, ENNReal.toReal_div]
    exact half_bound.trans half_le

/-- A strict loss gap makes the canonical normalization weight smaller than
the trace-density floor for all sufficiently small scales.  The threshold is
chosen before `delta`, as required when the critical sequence is invoked. -/
theorem exists_delta_proposition63CanonicalReentryWeight_le
    {densityLoss currentLoss weightLoss : ℝ}
    (loss_gap : densityLoss + currentLoss < weightLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        proposition63CanonicalReentryWeight delta weightLoss ≤
          (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta densityLoss *
            Kakeya.realRpowENN delta (currentLoss + 2) := by
  let gap : ℝ := weightLoss - currentLoss - densityLoss
  have gap_pos : 0 < gap := by
    dsimp only [gap]
    linarith
  let constant : ENNReal := 100
  have constant_ne_top : constant ≠ ⊤ := by
    norm_num [constant]
  rcases exists_delta_realRpowENN_bound constant constant_ne_top gap_pos with
    ⟨delta₀, delta₀_pos, delta₀_le_one, constant_absorb⟩
  refine ⟨delta₀, delta₀_pos, delta₀_le_one, ?_⟩
  intro delta delta_pos delta_le
  have gap_power_absorb :
      constant * Kakeya.realRpowENN delta gap ≤ 1 := by
    calc
      constant * Kakeya.realRpowENN delta gap ≤
          Kakeya.realRpowENN delta (-gap) *
            Kakeya.realRpowENN delta gap := by
        gcongr
        exact constant_absorb delta delta_pos delta_le
      _ = Kakeya.realRpowENN delta ((-gap) + gap) := by
        rw [realRpowENN_add delta_pos]
      _ = 1 := by simp [Kakeya.realRpowENN]
  have exponent_identity :
      weightLoss + 2 = gap + (densityLoss + (currentLoss + 2)) := by
    dsimp only [gap]
    ring
  have scaled :
      proposition63CanonicalReentryWeight delta weightLoss * 100 ≤
        Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta (currentLoss + 2) := by
    calc
      proposition63CanonicalReentryWeight delta weightLoss * 100 =
          (constant * Kakeya.realRpowENN delta gap) *
            Kakeya.realRpowENN delta (densityLoss + (currentLoss + 2)) := by
        unfold proposition63CanonicalReentryWeight constant
        rw [exponent_identity, realRpowENN_add delta_pos]
        ring
      _ ≤ 1 * Kakeya.realRpowENN delta
            (densityLoss + (currentLoss + 2)) := by gcongr
      _ = Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta (currentLoss + 2) := by
        rw [one_mul, realRpowENN_add delta_pos]
  have divided :
      proposition63CanonicalReentryWeight delta weightLoss ≤
        (Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta (currentLoss + 2)) / 100 :=
    (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
      (Or.inl (by norm_num))).2 scaled
  calc
    proposition63CanonicalReentryWeight delta weightLoss ≤
        (Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta (currentLoss + 2)) / 100 := divided
    _ = (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta (currentLoss + 2) := by
      rw [ENNReal.div_eq_inv_mul]
      ring

/-- A scale-count chosen solely from the normalization loss.  It is fixed
before the critical scale is selected. -/
noncomputable def proposition63CanonicalNearbyLevelCount
    (normalizationLoss : ℝ) : ℕ :=
  Nat.ceil (1 / normalizationLoss)

theorem proposition63CanonicalNearbyLevelCount_pos
    {normalizationLoss : ℝ}
    (normalizationLoss_pos : 0 < normalizationLoss) :
    0 < proposition63CanonicalNearbyLevelCount normalizationLoss := by
  exact Nat.ceil_pos.mpr (one_div_pos.mpr normalizationLoss_pos)

theorem proposition63CanonicalNearbyLevelCount_reaches
    {delta normalizationLoss : ℝ}
    (delta_pos : 0 < delta)
    (delta_le_one : delta ≤ 1)
    (normalizationLoss_pos : 0 < normalizationLoss) :
    ENNReal.ofReal (1 / delta) ≤
      Kakeya.realRpowENN delta (-normalizationLoss) ^
        proposition63CanonicalNearbyLevelCount normalizationLoss := by
  have count_bound :
      1 ≤ normalizationLoss *
        (proposition63CanonicalNearbyLevelCount normalizationLoss : ℝ) := by
    have ceil_bound :
        1 / normalizationLoss ≤
          (proposition63CanonicalNearbyLevelCount normalizationLoss : ℝ) :=
      Nat.le_ceil (1 / normalizationLoss)
    have scaled := mul_le_mul_of_nonneg_left ceil_bound
      normalizationLoss_pos.le
    field_simp [normalizationLoss_pos.ne'] at scaled ⊢
    exact scaled
  have power_bound :
      Real.rpow delta (-1) ≤
        Real.rpow delta
          (-(normalizationLoss *
            (proposition63CanonicalNearbyLevelCount
              normalizationLoss : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_ge delta_pos delta_le_one (by linarith)
  calc
    ENNReal.ofReal (1 / delta) =
        ENNReal.ofReal (Real.rpow delta (-1 : ℝ)) := by
      congr 1
      exact (one_div delta).trans (Real.rpow_neg_one delta).symm
    _ ≤ ENNReal.ofReal (Real.rpow delta
          (-(normalizationLoss *
            (proposition63CanonicalNearbyLevelCount
              normalizationLoss : ℝ)))) := ENNReal.ofReal_mono power_bound
    _ = Kakeya.realRpowENN delta (-normalizationLoss) ^
          proposition63CanonicalNearbyLevelCount normalizationLoss := by
      unfold Kakeya.realRpowENN
      rw [show -(normalizationLoss *
          (proposition63CanonicalNearbyLevelCount
            normalizationLoss : ℝ)) =
          (-normalizationLoss) *
            (proposition63CanonicalNearbyLevelCount
              normalizationLoss : ℝ) by ring]
      exact congrArg ENNReal.ofReal
        (Real.rpow_mul_natCast delta_pos.le (-normalizationLoss)
          (proposition63CanonicalNearbyLevelCount
            normalizationLoss)) |>.trans
          (ENNReal.ofReal_pow
            (Real.rpow_nonneg delta_pos.le (-normalizationLoss))
            (proposition63CanonicalNearbyLevelCount
              normalizationLoss))

theorem exists_delta_proposition63CanonicalNearbyAmbient_gt_two
    {normalizationLoss : ℝ}
    (normalizationLoss_pos : 0 < normalizationLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        (2 : ENNReal) <
          Kakeya.realRpowENN delta (-normalizationLoss) := by
  rcases exists_delta_realRpowENN_bound (3 : ENNReal) (by norm_num)
      normalizationLoss_pos with
    ⟨delta₀, delta₀_pos, delta₀_le_one, bound⟩
  exact ⟨delta₀, delta₀_pos, delta₀_le_one, fun delta delta_pos delta_le =>
    (by norm_num : (2 : ENNReal) < 3).trans_le
      (bound delta delta_pos delta_le)⟩

/-- A frozen critical normalization together with the two ordinary/cropped
certificates required by Proposition 6.3: grid-cell containment for the root
trace estimate, and one positive per-tube density which remains valid for
every later cubical subshading of the fixed ambient normalization. -/
structure Proposition63RootNormalizationData
    {sigma inputLoss outputLoss delta : ℝ}
    (source : PureWZ2ExtremalConfiguration sigma inputLoss delta)
    (normalizationExponent : ℕ)
    (densityLoss : ℝ) where
  normalization : PureWZ2CroppedCriticalNormalizationData
    (outputLoss := outputLoss) source normalizationExponent
  traceProvenance :
    Proposition63NormalizationTraceProvenance normalization
  ordinaryPerTube :
    ∀ index : Fin normalization.croppedFamily.card,
      Kakeya.realRpowENN delta densityLoss *
          volume (normalization.croppedFamily.tube index).carrier ≤
        volume (normalization.frame ''
          normalization.ordinaryRefined.carrier
            (PureWZ2CroppedCriticalNormalizationData.ordinaryIndex
              normalization
              (proposition63IdentitySubfamily
                normalization.croppedFamily) index))

/-- Package any provenance-complete cropped normalization as the root
companion for the Proposition 6.3 finite iterator.  The only additional
input is the scalar payment which weakens the normalization's built-in
`inputLoss / 2` ordinary-density lower bound to the chosen iterator density
loss. -/
noncomputable def Proposition63RootNormalizationData.ofNormalization
    {sigma delta inputLoss outputLoss densityLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := outputLoss) source normalizationExponent)
    (density_absorb :
      Kakeya.realRpowENN delta densityLoss ≤
        Kakeya.realRpowENN delta inputLoss / 2) :
    Proposition63RootNormalizationData
      (outputLoss := outputLoss) source normalizationExponent densityLoss := by
  refine
    { normalization := normalized
      traceProvenance :=
        { ordinary_cell_containment :=
            normalized.ordinary_cell_containment }
      ordinaryPerTube := ?_ }
  intro index
  have sourceDensity := normalized.framed_ordinary_per_tube
    (proposition63IdentitySubfamily normalized.croppedFamily) index
  calc
    Kakeya.realRpowENN delta densityLoss *
          volume (normalized.croppedFamily.tube index).carrier ≤
        (Kakeya.realRpowENN delta inputLoss / 2) *
          volume (normalized.croppedFamily.tube index).carrier := by
      gcongr
    _ ≤ volume
        (normalized.frame '' normalized.ordinaryRefined.carrier
          (PureWZ2CroppedCriticalNormalizationData.ordinaryIndex normalized
            (proposition63IdentitySubfamily normalized.croppedFamily) index)) := by
      simpa using sourceDensity

/-- Package Node 3's exact re-entry normalization as the root companion used
by the Proposition 6.3 finite iterator.  The only extra input is the explicit
scalar absorption which pays the factor `1 / 2` in Node 3's per-tube ordinary
density. -/
noncomputable def Proposition63RootNormalizationData.ofPropStickyReentry
    {sigma delta sourceLoss normalizationLoss densityLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {normalizationExponent : ℕ}
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss)
    (density_absorb :
      Kakeya.realRpowENN delta densityLoss ≤
        Kakeya.realRpowENN delta sourceLoss / 2) :
    Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) reentry.ordinarySource
      normalizationExponent densityLoss :=
  Proposition63RootNormalizationData.ofNormalization
    reentry.toNormalizationData density_absorb

/-- A strict gap between the Node 3 source loss and the iterator density loss
absorbs the factor `1 / 2` uniformly below one threshold.  The threshold is
chosen before the runtime normalization, preserving the critical-sequence
quantifier order. -/
theorem exists_delta_rootNormalization_of_propStickyReentry
    {sourceLoss densityLoss : ℝ}
    (loss_gap : sourceLoss < densityLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ {sigma normalizationLoss : ℝ}
          {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
          {croppedShading : WZ1PaperTubeShading croppedFamily}
          {normalizationExponent : ℕ},
          ∀ reentry : PureWZ2PropStickyReentryData
            (sigma := sigma) croppedShading normalizationExponent
            sourceLoss normalizationLoss,
            Nonempty (Proposition63RootNormalizationData
              (outputLoss := normalizationLoss) reentry.ordinarySource
              normalizationExponent densityLoss) := by
  rcases exists_delta_mul_rpow_le_rpow (2 : ℝ) (by norm_num) loss_gap with
    ⟨delta₀, delta₀_pos, delta₀_le_one, absorb⟩
  refine ⟨delta₀, delta₀_pos, delta₀_le_one, ?_⟩
  intro delta delta_pos delta_le sigma normalizationLoss croppedFamily
    croppedShading normalizationExponent reentry
  have absorbReal :
      2 * Real.rpow delta densityLoss ≤
        Real.rpow delta sourceLoss :=
    absorb delta delta_pos delta_le
  have absorbENN :
      (2 : ENNReal) * Kakeya.realRpowENN delta densityLoss ≤
        Kakeya.realRpowENN delta sourceLoss := by
    simp only [Kakeya.realRpowENN]
    rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_mono absorbReal
  have densityAbsorb :
      Kakeya.realRpowENN delta densityLoss ≤
        Kakeya.realRpowENN delta sourceLoss / 2 := by
    apply (ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)).2
    simpa [mul_comm] using absorbENN
  exact ⟨Proposition63RootNormalizationData.ofPropStickyReentry
    reentry densityAbsorb⟩

/-- Build the finite representative nearby-scale schedule directly from the
root normalization's pure CWA.  The output window is paid by the strict
two-level loss hierarchy. -/
theorem Proposition63RootNormalizationData.finiteNearbySchedule
    {sigma inputLoss normalizationLoss densityLoss reentryLoss delta : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss)
    (normalizationLoss_pos : 0 < normalizationLoss)
    (ambient_two :
      (2 : ENNReal) < Kakeya.realRpowENN delta (-normalizationLoss))
    (two_normalizationLoss_le : 2 * normalizationLoss ≤ reentryLoss) :
    Nonempty (WZ2PaperPureFiniteNearbyScheduleData
      (fine := root.normalization.croppedFamily)
      (Kakeya.realRpowENN delta (-normalizationLoss))
      (Kakeya.realRpowENN delta (-reentryLoss))
      (proposition63CanonicalNearbyLevelCount normalizationLoss)) := by
  have output_window :
      Kakeya.realRpowENN delta (-normalizationLoss) *
          Kakeya.realRpowENN delta (-normalizationLoss) ≤
        Kakeya.realRpowENN delta (-reentryLoss) := by
    rw [← realRpowENN_add root.normalization.final_extremal.delta_pos]
    exact realRpowENN_antitone root.normalization.final_extremal.delta_pos
      root.normalization.final_extremal.delta_le_one
      (by linarith)
  exact paper_pure_finite_nearby_schedule
    (proposition63CanonicalNearbyLevelCount normalizationLoss)
    root.normalization.final_extremal.delta_pos
    root.normalization.final_extremal.delta_le_one ambient_two
    root.normalization.final_extremal.cwa_nearby_scales.2.1.2
    (proposition63CanonicalNearbyLevelCount_reaches
      root.normalization.final_extremal.delta_pos
      root.normalization.final_extremal.delta_le_one normalizationLoss_pos)
    output_window root.normalization.final_extremal.cwa_nearby_scales

/-- The root-normalization interface used by Proposition 6.3.  Its
quantifiers agree with the historical normalization statement; only the
geometric provenance of the returned witness is strengthened. -/
def Proposition63RootNormalizationAt
    (normalizationExponent : ℕ) : Prop :=
  ∀ sigma : ℝ,
    PureWZ2CriticalPackage sigma →
      ∀ outputLoss densityLoss delta₀ : ℝ,
        0 < outputLoss → 0 < densityLoss → 0 < delta₀ →
          ∃ inputLoss delta : ℝ,
            0 < inputLoss ∧
            inputLoss ≤ outputLoss ∧
            0 < delta ∧ delta ≤ delta₀ ∧
            ∃ source : PureWZ2ExtremalConfiguration sigma inputLoss delta,
              Nonempty (Proposition63RootNormalizationData
                (outputLoss := outputLoss) source normalizationExponent
                  densityLoss)

/-- Forgetting the companion certificate recovers the historical Node 3
normalization interface. -/
theorem Proposition63RootNormalizationAt.toCroppedNormalizationAt
    {normalizationExponent : ℕ}
    (hroot : Proposition63RootNormalizationAt normalizationExponent) :
    PureWZ2CroppedCriticalNormalizationAt normalizationExponent := by
  intro sigma critical outputLoss delta₀ houtputLoss hdelta₀
  rcases hroot sigma critical outputLoss outputLoss delta₀ houtputLoss
      houtputLoss hdelta₀ with
    ⟨inputLoss, delta, hinputLoss, hinputLossLe, hdelta, hdeltaLe,
      source, ⟨root⟩⟩
  exact ⟨inputLoss, delta, hinputLoss, hinputLossLe, hdelta, hdeltaLe,
    source, ⟨root.normalization⟩⟩

/-- Cell-containment provenance is unchanged when the source and output
losses of a normalization are weakened: all geometric fields are retained
definitionally by `weaken_normalized_data`. -/
theorem Proposition63NormalizationTraceProvenance.weakenNormalizedData
    {sigma oldInputLoss newInputLoss oldOutputLoss newOutputLoss delta : ℝ}
    {normalizationExponent : ℕ}
    {source : PureWZ2ExtremalConfiguration sigma oldInputLoss delta}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := oldOutputLoss) source normalizationExponent}
    (provenance : Proposition63NormalizationTraceProvenance normalized)
    (inputLoss_le : oldInputLoss ≤ newInputLoss)
    (outputLoss_le : oldOutputLoss ≤ newOutputLoss)
    (newInputLoss_pos : 0 < newInputLoss)
    (newOutputLoss_pos : 0 < newOutputLoss)
    (delta_pos : 0 < delta)
    (delta_le_one : delta ≤ 1)
    (input_le_half : newInputLoss ≤ newOutputLoss / 2) :
    Proposition63NormalizationTraceProvenance
      (weaken_normalized_data normalized inputLoss_le outputLoss_le
        newInputLoss_pos newOutputLoss_pos delta_pos delta_le_one
        input_le_half) := by
  refine ⟨?_⟩
  intro index cell cellMeets
  exact provenance.ordinary_cell_containment index cell cellMeets

/-- The complete root companion is preserved by the loss-only weakening used
to match Node 3.  In particular, the ordinary density is attached to the
unchanged geometric normalization, not recomputed from the weaker losses. -/
noncomputable def Proposition63RootNormalizationData.weaken
    {sigma oldInputLoss newInputLoss oldOutputLoss newOutputLoss delta : ℝ}
    {normalizationExponent : ℕ}
    {densityLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma oldInputLoss delta}
    (root : Proposition63RootNormalizationData
      (outputLoss := oldOutputLoss) source normalizationExponent densityLoss)
    (inputLoss_le : oldInputLoss ≤ newInputLoss)
    (outputLoss_le : oldOutputLoss ≤ newOutputLoss)
    (newInputLoss_pos : 0 < newInputLoss)
    (newOutputLoss_pos : 0 < newOutputLoss)
    (delta_pos : 0 < delta)
    (delta_le_one : delta ≤ 1)
    (input_le_half : newInputLoss ≤ newOutputLoss / 2) :
    Proposition63RootNormalizationData
      (outputLoss := newOutputLoss)
      (weaken_extremal_configuration source inputLoss_le newInputLoss_pos
        delta_pos delta_le_one) normalizationExponent densityLoss where
  normalization := weaken_normalized_data root.normalization
    inputLoss_le outputLoss_le newInputLoss_pos newOutputLoss_pos
    delta_pos delta_le_one input_le_half
  traceProvenance := root.traceProvenance.weakenNormalizedData
    inputLoss_le outputLoss_le newInputLoss_pos newOutputLoss_pos
    delta_pos delta_le_one input_le_half
  ordinaryPerTube := by
    intro index
    exact root.ordinaryPerTube index

/-- The root companion discharges the geometric input of every finite
current-shading re-entry.  The remaining premises are exactly the accumulated
mass ledger, the finite nearby-scale schedule, and its scalar absorptions. -/
theorem Proposition63RootNormalizationData.currentShadingReentryOfMassLedger
    {sigma inputLoss normalizationLoss densityLoss currentLoss reentryLoss
      delta : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss)
    (current : WZ1PaperTubeShading root.normalization.croppedFamily)
    {leftProduct rightProduct : ENNReal}
    {ambientConstant outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := root.normalization.croppedFamily) ambientConstant
        outputConstant levelCount)
    (ambient_cwa : WZ2PaperPureCWAAtNearbyScales
      root.normalization.croppedFamily ambientConstant)
    (leftProduct_pos : 0 < leftProduct)
    (leftProduct_ne_top : leftProduct ≠ ⊤)
    (rightProduct_ne_top : rightProduct ≠ ⊤)
    (current_mass_ledger :
      leftProduct * root.normalization.croppedRefined.mass ≤
        rightProduct * current.mass)
    (normalizationLoss_le : normalizationLoss ≤ currentLoss)
    (currentLoss_le : currentLoss ≤ reentryLoss)
    (currentLoss_pos : 0 < currentLoss)
    (reentryNormalizationLoss : ℝ)
    (reentryNormalizationLoss_pos : 0 < reentryNormalizationLoss)
    (reentryLoss_le_half : reentryLoss ≤ reentryNormalizationLoss / 2)
    (mass_loss_absorb :
      proposition63Lemma43MassLoss leftProduct rightProduct *
          Kakeya.realRpowENN delta currentLoss ≤
        Kakeya.realRpowENN delta normalizationLoss)
    (normalizationWeight_le :
      normalizationWeight ≤
        (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta (currentLoss + 2))
    (normalization_weight_ne_zero : normalizationWeight ≠ 0)
    (normalization_weight_ne_top : normalizationWeight ≠ ⊤)
    (weightUpper_eq : weightUpper =
      (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
        Kakeya.realRpowENN delta 2)
    (output_finite : WZ2PaperFiniteErrorConstant outputConstant)
    (regularization_absorb :
      let degreeConstant :=
        16 * (schedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * root.normalization.croppedFamily.card) + 1 :
            ENNReal) ^ schedule.scaleCount
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * root.normalization.croppedFamily.card) + 1 :
            ENNReal) ^ (schedule.scaleCount + 1)
      max degreeConstant
          ((normalizationWeight⁻¹ *
              (ambientConstant *
                (regularizationLoss * weightUpper) *
                degreeConstant)) *
            ambientConstant) ≤
        outputConstant)
    (output_le : outputConstant ≤
      Kakeya.realRpowENN delta (-reentryLoss))
    (trace_scale_absorb :
      4 * (Kakeya.realRpowENN delta reentryLoss *
        Kakeya.deltaTubeVolume delta) ≤ normalizationWeight)
    (paper_scale_absorb : ∀ index,
      4 * (Kakeya.realRpowENN delta reentryLoss *
          volume (wz1PaperTubeCarrier
            (root.normalization.croppedFamily.tube index))) ≤
        (73 / 100 : ENNReal) * normalizationWeight)
    (current_sub_normalized : PaperIsSubshading current
      root.normalization.croppedRefined)
    (current_cubical : WZ1PaperIsCubicalShading current)
    (delta_small : delta ≤ 1 / 24)
    (ambient_top_level_constant : ENNReal)
    (ambient_top_level_cwa : WZ2PaperConvexWolffBound
      root.normalization.croppedFamily ambient_top_level_constant)
    (top_level_absorb :
      (normalizationWeight⁻¹ *
          (((8 : ENNReal) *
              (Nat.log 2 (2 * root.normalization.croppedFamily.card) + 1 :
                ENNReal) ^ (schedule.scaleCount + 1)) * weightUpper)) *
          ambient_top_level_constant ≤
        Kakeya.realRpowENN delta (-reentryLoss)) :
    ∃ data : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) root.normalization current,
      data.normalizationWeight = normalizationWeight ∧
        data.levelCount = levelCount ∧
        data.reentryNormalizationLoss = reentryNormalizationLoss := by
  exact proposition63_current_shading_reentry_of_density_and_mass_ledger
    root.normalization current schedule ambient_cwa leftProduct_pos
    leftProduct_ne_top rightProduct_ne_top current_mass_ledger
    normalizationLoss_le currentLoss_le currentLoss_pos
    reentryNormalizationLoss reentryNormalizationLoss_pos
    reentryLoss_le_half mass_loss_absorb
    root.ordinaryPerTube normalizationWeight_le normalization_weight_ne_zero
    normalization_weight_ne_top (by
      rw [weightUpper_eq]
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top)
        (by simp [Kakeya.realRpowENN])) (fun index => by
      rw [weightUpper_eq]
      exact proposition63_current_trace_weight_upper root.normalization
        current delta_small index) output_finite
    regularization_absorb output_le trace_scale_absorb paper_scale_absorb
    current_sub_normalized current_cubical root.normalization.line_class
    delta_small ambient_top_level_constant ambient_top_level_cwa
    top_level_absorb

/-- Canonical-weight specialization of the root mass-ledger adapter.  All
geometric lower and upper weight bounds are discharged internally; only the
single loss-gap upper absorption and the schedule-level costs remain. -/
theorem Proposition63RootNormalizationData.currentShadingReentryCanonical
    {sigma inputLoss normalizationLoss densityLoss currentLoss weightLoss
      reentryLoss delta : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss)
    (current : WZ1PaperTubeShading root.normalization.croppedFamily)
    {leftProduct rightProduct ambientConstant outputConstant : ENNReal}
    {levelCount : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := root.normalization.croppedFamily) ambientConstant
        outputConstant levelCount)
    (ambient_cwa : WZ2PaperPureCWAAtNearbyScales
      root.normalization.croppedFamily ambientConstant)
    (leftProduct_pos : 0 < leftProduct)
    (leftProduct_ne_top : leftProduct ≠ ⊤)
    (rightProduct_ne_top : rightProduct ≠ ⊤)
    (current_mass_ledger :
      leftProduct * root.normalization.croppedRefined.mass ≤
        rightProduct * current.mass)
    (normalizationLoss_le : normalizationLoss ≤ currentLoss)
    (currentLoss_le : currentLoss ≤ reentryLoss)
    (currentLoss_pos : 0 < currentLoss)
    (reentryNormalizationLoss : ℝ)
    (reentryNormalizationLoss_pos : 0 < reentryNormalizationLoss)
    (reentryLoss_le_half : reentryLoss ≤ reentryNormalizationLoss / 2)
    (mass_loss_absorb :
      proposition63Lemma43MassLoss leftProduct rightProduct *
          Kakeya.realRpowENN delta currentLoss ≤
        Kakeya.realRpowENN delta normalizationLoss)
    (canonical_weight_absorb :
      proposition63CanonicalReentryWeight delta weightLoss ≤
        (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta (currentLoss + 2))
    (trace_fixed_absorb :
      (96 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta (reentryLoss - weightLoss) ≤ 1)
    (paper_fixed_absorb :
      ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta (reentryLoss - weightLoss) ≤
        (73 / 100 : ENNReal))
    (output_finite : WZ2PaperFiniteErrorConstant outputConstant)
    (regularization_absorb :
      let degreeConstant :=
        16 * (schedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * root.normalization.croppedFamily.card) + 1 :
            ENNReal) ^ schedule.scaleCount
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * root.normalization.croppedFamily.card) + 1 :
            ENNReal) ^ (schedule.scaleCount + 1)
      max degreeConstant
          (((proposition63CanonicalReentryWeight delta weightLoss)⁻¹ *
              (ambientConstant *
                (regularizationLoss *
                  ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
                    Kakeya.realRpowENN delta 2)) *
                degreeConstant)) *
            ambientConstant) ≤
        outputConstant)
    (output_le : outputConstant ≤
      Kakeya.realRpowENN delta (-reentryLoss))
    (current_sub_normalized : PaperIsSubshading current
      root.normalization.croppedRefined)
    (current_cubical : WZ1PaperIsCubicalShading current)
    (delta_small : delta ≤ 1 / 24)
    (ambient_top_level_constant : ENNReal)
    (ambient_top_level_cwa : WZ2PaperConvexWolffBound
      root.normalization.croppedFamily ambient_top_level_constant)
    (top_level_absorb :
      ((proposition63CanonicalReentryWeight delta weightLoss)⁻¹ *
          (((8 : ENNReal) *
              (Nat.log 2 (2 * root.normalization.croppedFamily.card) + 1 :
                ENNReal) ^ (schedule.scaleCount + 1)) *
            ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN delta 2))) *
          ambient_top_level_constant ≤
        Kakeya.realRpowENN delta (-reentryLoss)) :
    ∃ data : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) root.normalization current,
      data.normalizationWeight =
          proposition63CanonicalReentryWeight delta weightLoss ∧
        data.levelCount = levelCount ∧
        data.reentryNormalizationLoss = reentryNormalizationLoss := by
  apply root.currentShadingReentryOfMassLedger current schedule ambient_cwa
    leftProduct_pos leftProduct_ne_top rightProduct_ne_top
    current_mass_ledger normalizationLoss_le currentLoss_le currentLoss_pos
    reentryNormalizationLoss reentryNormalizationLoss_pos
    reentryLoss_le_half mass_loss_absorb canonical_weight_absorb
    (proposition63CanonicalReentryWeight_ne_zero root.normalization.final_extremal.delta_pos)
    (proposition63CanonicalReentryWeight_ne_top) rfl output_finite
    regularization_absorb output_le
    (proposition63CanonicalReentryWeight_trace_scale
      root.normalization.final_extremal.delta_pos
      root.normalization.final_extremal.delta_le_one trace_fixed_absorb)
    (fun index => proposition63CanonicalReentryWeight_paper_scale
      root.normalization.final_extremal.delta_pos delta_small
      paper_fixed_absorb root.normalization.line_class index)
    current_sub_normalized current_cubical delta_small
    ambient_top_level_constant ambient_top_level_cwa top_level_absorb

/-- The external regularizer's closure inequality dominates the smaller
top-level CWA transfer cost whenever the ambient constant is greater than
two and the finite schedule is nonempty. -/
theorem proposition63_topLevelAbsorb_of_regularizationAbsorb
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := family) ambientConstant outputConstant levelCount)
    (ambient_two : (2 : ENNReal) < ambientConstant)
    (regularization_absorb :
      let degreeConstant :=
        16 * (schedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
            schedule.scaleCount
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
            (schedule.scaleCount + 1)
      max degreeConstant
          ((normalizationWeight⁻¹ *
              (ambientConstant *
                (regularizationLoss * weightUpper) *
                degreeConstant)) *
            ambientConstant) ≤
        outputConstant) :
    (normalizationWeight⁻¹ *
        (((8 : ENNReal) *
          (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
            (schedule.scaleCount + 1)) * weightUpper)) *
      ambientConstant ≤ outputConstant := by
  let degreeConstant : ENNReal :=
    16 * (schedule.scaleCount : ENNReal) *
      (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^ schedule.scaleCount
  let regularizationLoss : ENNReal :=
    (8 : ENNReal) *
      (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
        (schedule.scaleCount + 1)
  have ambient_one : (1 : ENNReal) ≤ ambientConstant :=
    (by norm_num : (1 : ENNReal) < 2).le.trans ambient_two.le
  have count_one : (1 : ENNReal) ≤ schedule.scaleCount := by
    exact_mod_cast schedule.scaleCount_pos
  have log_one : (1 : ENNReal) ≤
      (Nat.log 2 (2 * family.card) + 1 : ENNReal) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have degree_one : (1 : ENNReal) ≤ degreeConstant := by
    dsimp only [degreeConstant]
    calc
      (1 : ENNReal) ≤ 16 * 1 * 1 := by norm_num
      _ ≤ 16 * (schedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
            schedule.scaleCount := by
        gcongr
        exact one_le_pow₀ log_one
  have dominated :
      (normalizationWeight⁻¹ * (regularizationLoss * weightUpper)) *
          ambientConstant ≤
        (normalizationWeight⁻¹ *
          (ambientConstant * (regularizationLoss * weightUpper) *
            degreeConstant)) * ambientConstant := by
    calc
      (normalizationWeight⁻¹ * (regularizationLoss * weightUpper)) *
            ambientConstant =
          ((normalizationWeight⁻¹ * (regularizationLoss * weightUpper)) *
            ambientConstant) * 1 := by simp
      _ ≤ ((normalizationWeight⁻¹ * (regularizationLoss * weightUpper)) *
            ambientConstant) * (ambientConstant * degreeConstant) := by
        gcongr
        calc
          (1 : ENNReal) ≤ 1 * 1 := by simp
          _ ≤ ambientConstant * degreeConstant := by gcongr
      _ = (normalizationWeight⁻¹ *
          (ambientConstant * (regularizationLoss * weightUpper) *
            degreeConstant)) * ambientConstant := by ring
  exact dominated.trans <|
    (le_max_right degreeConstant _).trans regularization_absorb

/-- Prepare a fresh Node 3 re-entry directly from the extremality of the
current shading.  This is the one-scale-iteration form: the preceding step
has already restored extremality, so no prefix product of earlier raw mass
losses is needed.  The fixed root normalization is used only for its ordinary
trace provenance and ambient family. -/
theorem Proposition63RootNormalizationData.currentShadingReentryFromExtremal
    {sigma inputLoss normalizationLoss densityLoss currentLoss weightLoss
      reentryLoss delta : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss)
    (current : WZ1PaperTubeShading root.normalization.croppedFamily)
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := root.normalization.croppedFamily)
      (Kakeya.realRpowENN delta (-normalizationLoss))
      (Kakeya.realRpowENN delta (-reentryLoss))
      (proposition63CanonicalNearbyLevelCount normalizationLoss))
    (ambient_two : (2 : ENNReal) <
      Kakeya.realRpowENN delta (-normalizationLoss))
    (current_extremal : WZ2PaperCroppedIsExtremal sigma currentLoss
      root.normalization.croppedFamily current)
    (currentLoss_le_reentry : currentLoss ≤ reentryLoss)
    (currentLoss_pos : 0 < currentLoss)
    (reentryNormalizationLoss : ℝ)
    (reentryNormalizationLoss_pos : 0 < reentryNormalizationLoss)
    (reentryLoss_le_half : reentryLoss ≤ reentryNormalizationLoss / 2)
    (canonical_weight_absorb :
      proposition63CanonicalReentryWeight delta weightLoss ≤
        (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta (currentLoss + 2))
    (trace_fixed_absorb :
      (96 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta (reentryLoss - weightLoss) ≤ 1)
    (paper_fixed_absorb :
      ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta (reentryLoss - weightLoss) ≤
        (73 / 100 : ENNReal))
    (regularization_absorb :
      let degreeConstant :=
        16 * (schedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * root.normalization.croppedFamily.card) + 1 :
            ENNReal) ^ schedule.scaleCount
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * root.normalization.croppedFamily.card) + 1 :
            ENNReal) ^ (schedule.scaleCount + 1)
      max degreeConstant
          (((proposition63CanonicalReentryWeight delta weightLoss)⁻¹ *
              (Kakeya.realRpowENN delta (-normalizationLoss) *
                (regularizationLoss *
                  ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
                    Kakeya.realRpowENN delta 2)) *
                degreeConstant)) *
            Kakeya.realRpowENN delta (-normalizationLoss)) ≤
        Kakeya.realRpowENN delta (-reentryLoss))
    (current_sub_normalized : PaperIsSubshading current
      root.normalization.croppedRefined)
    (current_cubical : WZ1PaperIsCubicalShading current)
    (delta_small : delta ≤ 1 / 24) :
    ∃ data : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) root.normalization current,
      data.normalizationWeight =
          proposition63CanonicalReentryWeight delta weightLoss ∧
        data.weightUpper =
          (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2 ∧
        data.levelCount =
          proposition63CanonicalNearbyLevelCount normalizationLoss ∧
        data.reentryNormalizationLoss = reentryNormalizationLoss := by
  have reentry_extremal : WZ2PaperCroppedIsExtremal sigma reentryLoss
      root.normalization.croppedFamily current :=
    current_extremal.mono_loss currentLoss_le_reentry
  have traceBounds :=
    proposition63_current_trace_bounds_of_per_tube_density_and_extremal
      root.normalization current current_sub_normalized current_cubical
      current_extremal currentLoss_pos root.normalization.line_class
      delta_small (Kakeya.realRpowENN delta densityLoss)
      (proposition63CanonicalReentryWeight delta weightLoss)
      root.ordinaryPerTube canonical_weight_absorb
  have output_finite : WZ2PaperFiniteErrorConstant
      (Kakeya.realRpowENN delta (-reentryLoss)) :=
    reentry_extremal.cwa_nearby_scales.2.1
  have top_level_absorb :=
    proposition63_topLevelAbsorb_of_regularizationAbsorb schedule
      ambient_two regularization_absorb
  exact proposition63_current_shading_reentry root.normalization current
    schedule root.normalization.final_extremal.cwa_nearby_scales
    reentry_extremal reentryNormalizationLoss
    reentryNormalizationLoss_pos reentryLoss_le_half
    (proposition63CanonicalReentryWeight_ne_zero current_extremal.delta_pos)
    proposition63CanonicalReentryWeight_ne_top
    (by
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top)
        (by simp [Kakeya.realRpowENN]))
    traceBounds.1
    (fun index => proposition63_current_trace_weight_upper
      root.normalization current delta_small index)
    output_finite regularization_absorb le_rfl
    (proposition63CanonicalReentryWeight_trace_scale
      current_extremal.delta_pos current_extremal.delta_le_one
      trace_fixed_absorb)
    (fun index => proposition63CanonicalReentryWeight_paper_scale
      current_extremal.delta_pos delta_small paper_fixed_absorb
      root.normalization.line_class index)
    current_sub_normalized current_cubical traceBounds.2
    root.normalization.line_class delta_small
    (Kakeya.realRpowENN delta (-normalizationLoss))
    root.normalization.cropped_top_level_cwa top_level_absorb

/-- Fully canonical structural preparation of one finite re-entry step.
The root extremality supplies both CWA inputs and the output finite-error
certificate; the regularizer's main absorption also pays the top-level CWA
transfer. -/
theorem Proposition63RootNormalizationData.currentShadingReentryFromRoot
    {sigma inputLoss normalizationLoss densityLoss currentLoss weightLoss
      reentryLoss delta : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss)
    (current : WZ1PaperTubeShading root.normalization.croppedFamily)
    {leftProduct rightProduct : ENNReal}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := root.normalization.croppedFamily)
      (Kakeya.realRpowENN delta (-normalizationLoss))
      (Kakeya.realRpowENN delta (-reentryLoss))
      (proposition63CanonicalNearbyLevelCount normalizationLoss))
    (ambient_two : (2 : ENNReal) <
      Kakeya.realRpowENN delta (-normalizationLoss))
    (leftProduct_pos : 0 < leftProduct)
    (leftProduct_ne_top : leftProduct ≠ ⊤)
    (rightProduct_ne_top : rightProduct ≠ ⊤)
    (current_mass_ledger :
      leftProduct * root.normalization.croppedRefined.mass ≤
        rightProduct * current.mass)
    (normalizationLoss_le : normalizationLoss ≤ currentLoss)
    (currentLoss_le : currentLoss ≤ reentryLoss)
    (currentLoss_pos : 0 < currentLoss)
    (reentryNormalizationLoss : ℝ)
    (reentryNormalizationLoss_pos : 0 < reentryNormalizationLoss)
    (reentryLoss_le_half : reentryLoss ≤ reentryNormalizationLoss / 2)
    (mass_loss_absorb :
      proposition63Lemma43MassLoss leftProduct rightProduct *
          Kakeya.realRpowENN delta currentLoss ≤
        Kakeya.realRpowENN delta normalizationLoss)
    (canonical_weight_absorb :
      proposition63CanonicalReentryWeight delta weightLoss ≤
        (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta (currentLoss + 2))
    (trace_fixed_absorb :
      (96 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta (reentryLoss - weightLoss) ≤ 1)
    (paper_fixed_absorb :
      ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta (reentryLoss - weightLoss) ≤
        (73 / 100 : ENNReal))
    (regularization_absorb :
      let degreeConstant :=
        16 * (schedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * root.normalization.croppedFamily.card) + 1 :
            ENNReal) ^ schedule.scaleCount
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * root.normalization.croppedFamily.card) + 1 :
            ENNReal) ^ (schedule.scaleCount + 1)
      max degreeConstant
          (((proposition63CanonicalReentryWeight delta weightLoss)⁻¹ *
              (Kakeya.realRpowENN delta (-normalizationLoss) *
                (regularizationLoss *
                  ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
                    Kakeya.realRpowENN delta 2)) *
                degreeConstant)) *
            Kakeya.realRpowENN delta (-normalizationLoss)) ≤
        Kakeya.realRpowENN delta (-reentryLoss))
    (current_sub_normalized : PaperIsSubshading current
      root.normalization.croppedRefined)
    (current_cubical : WZ1PaperIsCubicalShading current)
    (delta_small : delta ≤ 1 / 24) :
    ∃ data : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) root.normalization current,
      data.normalizationWeight =
          proposition63CanonicalReentryWeight delta weightLoss ∧
        data.levelCount =
          proposition63CanonicalNearbyLevelCount normalizationLoss ∧
        data.reentryNormalizationLoss = reentryNormalizationLoss := by
  have output_finite : WZ2PaperFiniteErrorConstant
      (Kakeya.realRpowENN delta (-reentryLoss)) :=
    (root.normalization.final_extremal.mono_loss
      (normalizationLoss_le.trans currentLoss_le)).cwa_nearby_scales.2.1
  have top_level_absorb :=
    proposition63_topLevelAbsorb_of_regularizationAbsorb schedule
      ambient_two regularization_absorb
  exact root.currentShadingReentryCanonical current schedule
    root.normalization.final_extremal.cwa_nearby_scales leftProduct_pos
    leftProduct_ne_top rightProduct_ne_top current_mass_ledger
    normalizationLoss_le currentLoss_le currentLoss_pos
    reentryNormalizationLoss reentryNormalizationLoss_pos
    reentryLoss_le_half mass_loss_absorb
    canonical_weight_absorb trace_fixed_absorb paper_fixed_absorb
    output_finite regularization_absorb le_rfl current_sub_normalized
    current_cubical delta_small
    (Kakeya.realRpowENN delta (-normalizationLoss))
    root.normalization.cropped_top_level_cwa top_level_absorb

/- Select the root normalization only after Node 3 has exposed its input
loss, while retaining the companion trace provenance through the two loss
views.  The cropped family and shading used by `base`, `normalized`, and both
sticky provisions are definitionally the same. -/
/-
theorem proposition63_root_normalization_with_sticky_pair_at
    {normalizationExponent logExponent : ℕ}
    (hRootAt : Proposition63RootNormalizationAt normalizationExponent)
    (hStickyAt : PureWZ2CroppedPropStickyAt
      normalizationExponent logExponent)
    (sigma : ℝ)
    (critical : PureWZ2CriticalPackage sigma)
    (normalizationLoss densityLoss outputLoss externalDeltaBound : ℝ)
    (normalizationLoss_pos : 0 < normalizationLoss)
    (densityLoss_pos : 0 < densityLoss)
    (normalizationLoss_le : normalizationLoss ≤ outputLoss)
    (externalDeltaBound_pos : 0 < externalDeltaBound) :
    ∃ (stickyInputLoss delta : ℝ)
      (source : PureWZ2ExtremalConfiguration sigma stickyInputLoss delta)
      (_root : Proposition63RootNormalizationData
        (outputLoss := stickyInputLoss) source normalizationExponent
          densityLoss)
      (base : PureWZ2GrainBaseConfig sigma normalizationLoss delta)
      (_reentryProvision :
        ∀ reentrySource : PureWZ2ExtremalConfiguration
            sigma stickyInputLoss delta,
          ∀ reentryNormalized : PureWZ2CroppedCriticalNormalizationData
            (outputLoss := stickyInputLoss) reentrySource
              normalizationExponent,
            ∀ rho : WZ2PaperRequestedScale delta,
              Real.rpow delta (1 - normalizationLoss) ≤ rho.1 →
              rho.1 ≤ Real.rpow delta normalizationLoss →
                Nonempty (PureWZ2PropStickyData
                  (sigma := sigma) (outputLoss := normalizationLoss)
                  reentryNormalized.croppedRefined rho logExponent))
      (_normalizationProvision : PureWZ2RestrictedStickyProvisionFor
        delta base.family base.shading sigma normalizationLoss logExponent)
      (_outputProvision : PureWZ2RestrictedStickyProvisionFor
        delta base.family base.shading sigma outputLoss logExponent),
      0 < stickyInputLoss ∧ 0 < delta ∧ delta ≤ externalDeltaBound := by
  rcases hStickyAt sigma critical normalizationLoss
      normalizationLoss_pos with
    ⟨stickyInputLoss, stickyDeltaBound, stickyInputLoss_pos,
      stickyDeltaBound_pos, _stickyDeltaBound_le_one, stickyAt⟩
  let commonDeltaBound : ℝ := min externalDeltaBound stickyDeltaBound
  have commonDeltaBound_pos : 0 < commonDeltaBound := by
    exact lt_min externalDeltaBound_pos stickyDeltaBound_pos
  have commonDeltaBound_le_external :
      commonDeltaBound ≤ externalDeltaBound := min_le_left _ _
  have commonDeltaBound_le_sticky :
      commonDeltaBound ≤ stickyDeltaBound := min_le_right _ _
  let targetLoss : ℝ := min stickyInputLoss normalizationLoss
  have targetLoss_pos : 0 < targetLoss := by
    exact lt_min stickyInputLoss_pos normalizationLoss_pos
  have targetLoss_le_sticky : targetLoss ≤ stickyInputLoss :=
    min_le_left _ _
  have targetLoss_le_normalization : targetLoss ≤ normalizationLoss :=
    min_le_right _ _
  rcases hRootAt sigma critical targetLoss densityLoss commonDeltaBound
      targetLoss_pos densityLoss_pos commonDeltaBound_pos with
    ⟨rootInputLoss, delta, rootInputLoss_pos, rootInputLoss_le, delta_pos,
      delta_le, rootSource, ⟨root⟩⟩
  have delta_le_one : delta ≤ 1 :=
    root.normalization.final_extremal.delta_le_one
  let source : PureWZ2ExtremalConfiguration sigma stickyInputLoss delta :=
    weaken_extremal_configuration rootSource
      (rootInputLoss_le.trans targetLoss_le_sticky) stickyInputLoss_pos
      delta_pos delta_le_one
  let weakenedRoot : Proposition63RootNormalizationData
      (outputLoss := stickyInputLoss) source normalizationExponent
        densityLoss :=
    root.weaken
      (rootInputLoss_le.trans targetLoss_le_sticky) targetLoss_le_sticky
      stickyInputLoss_pos stickyInputLoss_pos delta_pos delta_le_one le_rfl
  have baseExtremal : WZ2PaperCroppedIsExtremal sigma normalizationLoss
      root.normalization.croppedFamily root.normalization.croppedRefined :=
    root.normalization.final_extremal.mono_loss
      targetLoss_le_normalization
  have baseTopLevelCWA : WZ2PaperConvexWolffBound
      root.normalization.croppedFamily
      (Kakeya.realRpowENN delta (-normalizationLoss)) := by
    have coefficient_le :
        Kakeya.realRpowENN delta (-targetLoss) ≤
          Kakeya.realRpowENN delta (-normalizationLoss) := by
      apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_exponent_ge delta_pos (by linarith)
        (by linarith)
    intro convexSet convexSet_convex
    exact (root.normalization.cropped_top_level_cwa convexSet
      convexSet_convex).trans (by gcongr)
  let base : PureWZ2GrainBaseConfig sigma normalizationLoss delta :=
    { family := root.normalization.croppedFamily
      shading := root.normalization.croppedRefined
      line_class := root.normalization.line_class
      cubical := root.normalization.cropped_cubical
      extremal := baseExtremal
      top_level_cwa := baseTopLevelCWA }
  have reentryProvision :
      ∀ reentrySource : PureWZ2ExtremalConfiguration
          sigma stickyInputLoss delta,
        ∀ reentryNormalized : PureWZ2CroppedCriticalNormalizationData
          (outputLoss := stickyInputLoss) reentrySource
            normalizationExponent,
          ∀ rho : WZ2PaperRequestedScale delta,
            Real.rpow delta (1 - normalizationLoss) ≤ rho.1 →
            rho.1 ≤ Real.rpow delta normalizationLoss →
              Nonempty (PureWZ2PropStickyData
                (sigma := sigma) (outputLoss := normalizationLoss)
                reentryNormalized.croppedRefined rho logExponent) := by
    exact stickyAt delta delta_pos
      (delta_le.trans commonDeltaBound_le_sticky)
  have normalizationProvision : PureWZ2RestrictedStickyProvisionFor
      delta base.family base.shading sigma normalizationLoss logExponent := by
    intro rho rho_lower rho_upper
    exact reentryProvision source weakenedRoot.normalization rho rho_lower
      rho_upper
  have outputProvision : PureWZ2RestrictedStickyProvisionFor
      delta base.family base.shading sigma outputLoss logExponent :=
    normalizationProvision.mono_loss normalizationLoss_le delta_pos
      delta_le_one
  exact ⟨stickyInputLoss, delta, source, weakenedRoot, base,
    reentryProvision, normalizationProvision, outputProvision,
    stickyInputLoss_pos, delta_pos,
    delta_le.trans commonDeltaBound_le_external⟩
-/

end Kakeya.Assouad.PureWZ2

end
