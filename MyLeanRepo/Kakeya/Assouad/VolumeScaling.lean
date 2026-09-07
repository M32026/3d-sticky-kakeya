import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Volume scaling and measure transport for homotheties

Infrastructure for applying a homothety `x ↦ c • x` to tube families and shadings.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

/-- The homothety centered at the origin with scale `c`, as a continuous linear map. -/
def homothetyLin (c : ℝ) : Point3 →L[ℝ] Point3 :=
  { toFun := fun x => c • x
    map_add' := by intro x y; exact smul_add c x y
    map_smul' := by intro r x; simp [smul_smul] <;> ring
    cont := continuous_const.smul continuous_id }

/-- The homothety function. -/
def homothety (c : ℝ) : Point3 → Point3 := homothetyLin c

lemma homothety_apply (c : ℝ) (x : Point3) :
    homothety c x = c • x := rfl

/-- Determinant of the homothety linear map in dimension 3. -/
lemma homothetyLin_det (c : ℝ) :
    LinearMap.det (homothetyLin c : Point3 →ₗ[ℝ] Point3) = c ^ 3 := by
  have h : (homothetyLin c : Point3 →ₗ[ℝ] Point3) =
      c • (LinearMap.id : Point3 →ₗ[ℝ] Point3) := by
    ext x
    simp [homothetyLin]
    <;> rfl
  rw [h]
  simpa [LinearMap.det_smul] using by ring

/-- Volume scaling under homothety: `volume (c • S) = c^3 * volume S`. -/
lemma volume_homothety (c : ℝ) (hc : 0 < c) (S : Set Point3) :
    volume (homothety c '' S) =
      ENNReal.ofReal (c ^ 3) * volume S := by
  let L : Point3 →L[ℝ] Point3 := homothetyLin c
  have h_det : |LinearMap.det (L : Point3 →ₗ[ℝ] Point3)| = c ^ 3 := by
    rw [homothetyLin_det c]
    have hpos : 0 ≤ c ^ 3 := by positivity
    rw [abs_of_nonneg hpos]
  have h_main : volume (L '' S) =
      ENNReal.ofReal |LinearMap.det (L : Point3 →ₗ[ℝ] Point3)| * volume S :=
    MeasureTheory.Measure.addHaar_image_continuousLinearMap volume L S
  exact h_main.trans (by rw [h_det])

/-- Homothety preserves measurable sets. -/
lemma measurableSet_homothety (c : ℝ) (hc : c ≠ 0)
    {S : Set Point3} (hS : MeasurableSet S) :
    MeasurableSet (homothety c '' S) := by
  have h_eq : homothety c '' S = (homothety c⁻¹) ⁻¹' S := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h_comp : (homothety c⁻¹) ((homothety c) x) = x := by
        simp only [homothety]
        calc
          c⁻¹ • (c • x) = (c⁻¹ * c) • x := by rw [smul_smul]
          _ = (1 : ℝ) • x := by rw [inv_mul_cancel₀ hc]
          _ = x := by simp
      rw [h_comp]
      exact hx
    · intro hy
      refine ⟨homothety c⁻¹ y, hy, ?_⟩
      have h_comp : (homothety c) ((homothety c⁻¹) y) = y := by
        simp only [homothety]
        calc
          c • (c⁻¹ • y) = (c * c⁻¹) • y := by rw [smul_smul]
          _ = (1 : ℝ) • y := by rw [mul_inv_cancel₀ hc]
          _ = y := by simp
      exact h_comp
  rw [h_eq]
  exact (homothetyLin c⁻¹).continuous.measurable hS

/-- Image of an indexed union under homothety. -/
lemma homothety_image_iUnion {ι : Type*} (c : ℝ) (s : ι → Set Point3) :
    homothety c '' (⋃ i, s i) = ⋃ i, homothety c '' s i := by
  ext y
  simp only [Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨x, ⟨i, hx⟩, rfl⟩
    exact ⟨i, x, hx, rfl⟩
  · rintro ⟨i, x, hx, rfl⟩
    exact ⟨x, ⟨i, hx⟩, rfl⟩

/-- Image of a shading union under homothety. -/
lemma homothety_shading_union {δ : ℝ} {F : Streamlined.TubeFamily δ}
    (Y : Streamlined.TubeShading F) (c : ℝ) :
    homothety c '' Y.union = ⋃ i : Fin F.card, homothety c '' Y.carrier i := by
  have h1 : Y.union = ⋃ i : Fin F.card, Y.carrier i := by
    ext x
    simp [Streamlined.Shading.union]
    <;> tauto
  rw [h1]
  exact homothety_image_iUnion c (fun i => Y.carrier i)

/-- Homothety is injective for nonzero scale. -/
lemma homothety_injective (c : ℝ) (hc : c ≠ 0) :
    Function.Injective (homothety c) := by
  intro x y h
  have h' : c • x = c • y := h
  exact smul_right_injective _ hc h'

/-- Midpoint of a DeltaTube's unit segment. -/
def deltaTubeMidpoint {δ : ℝ} (T : Kakeya.DeltaTube δ) : Point3 :=
  T.base + (1 / 2 : ℝ) • T.direction

/--
Normalize a DeltaTube by scaling its midpoint by `c` while keeping direction
and using radius `c * δ`. The new unit segment is centered at `c • midpoint`.

For `0 < c ≤ 1`, the new tube carrier CONTAINS the homothety image of the original
carrier, because the original segment (length 1) scales to length `c`, while the
new segment has length 1 centered at the same midpoint.
-/
def normalizeDeltaTube {δ : ℝ} (T : Kakeya.DeltaTube δ) (c : ℝ) :
    Kakeya.DeltaTube (c * δ) where
  base := c • deltaTubeMidpoint T - (1 / 2 : ℝ) • T.direction
  direction := T.direction
  direction_unit := T.direction_unit

/-- The unit segment is compact. -/
lemma unitSegment_compact {base direction : Point3} :
    IsCompact (Kakeya.unitSegment base direction) := by
  apply IsCompact.image isCompact_Icc
  fun_prop

/--
For `0 < c ≤ 1`, the normalized tube carrier contains the homothety image
of the original tube carrier.
-/
lemma normalizeDeltaTube_carrier_contains
    {δ : ℝ} (hδ : 0 ≤ δ) (T : Kakeya.DeltaTube δ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    homothety c '' T.carrier ⊆ (normalizeDeltaTube T c).carrier := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hcarrier : T.carrier = Metric.cthickening δ (Kakeya.unitSegment T.base T.direction) := by
    rfl
  rw [hcarrier] at hx
  have h_seg_compact : IsCompact (Kakeya.unitSegment T.base T.direction) :=
    unitSegment_compact
  rw [h_seg_compact.cthickening_eq_biUnion_closedBall hδ] at hx
  have h_exists : ∃ (z : Point3), z ∈ Kakeya.unitSegment T.base T.direction ∧ x ∈ Metric.closedBall z δ := by
    simpa [Set.mem_iUnion] using hx
  rcases h_exists with ⟨z, hz, hxz⟩
  rcases hz with ⟨t, ht, hz_eq⟩
  have h_base : (normalizeDeltaTube T c).base =
      c • deltaTubeMidpoint T - (1 / 2 : ℝ) • T.direction := by rfl
  have h_dir : (normalizeDeltaTube T c).direction = T.direction := by rfl
  let s : ℝ := 1 / 2 + c * (t - 1 / 2)
  have hs1 : 0 ≤ s := by
    dsimp only [s]
    have hc' : 0 ≤ c := by linarith
    have h5 : -1 / 2 ≤ t - 1 / 2 := by linarith [ht.1]
    have h6 : c * (-1 / 2) ≤ c * (t - 1 / 2) := mul_le_mul_of_nonneg_left h5 hc'
    have h1 : c * (t - 1 / 2) ≥ -c / 2 := by
      have h_eq : c * (-1 / 2) = -c / 2 := by ring
      rw [h_eq] at h6
      exact h6
    have h2 : (1 : ℝ) / 2 - c / 2 ≥ 0 := by linarith [hc1]
    linarith
  have hs2 : s ≤ 1 := by
    dsimp only [s]
    have hc' : 0 ≤ c := by linarith
    have h5 : t - 1 / 2 ≤ 1 / 2 := by linarith [ht.2]
    have h6 : c * (t - 1 / 2) ≤ c * (1 / 2) := mul_le_mul_of_nonneg_left h5 hc'
    have h1 : c * (t - 1 / 2) ≤ c / 2 := by
      have h_eq : c * (1 / 2) = c / 2 := by ring
      rw [h_eq] at h6
      exact h6
    have h2 : (1 : ℝ) / 2 + c / 2 ≤ 1 := by linarith [hc1]
    linarith
  have hsz : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs1, hs2⟩
  have h_z'_eq : (normalizeDeltaTube T c).base + s • T.direction = c • (T.base + t • T.direction) := by
    rw [h_base]
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [deltaTubeMidpoint, s, smul_add, smul_smul, add_smul, sub_smul] <;> ring
  have h_z'_in_seg : c • (T.base + t • T.direction) ∈ Kakeya.unitSegment
      (normalizeDeltaTube T c).base (normalizeDeltaTube T c).direction := by
    refine ⟨s, hsz, ?_⟩
    rw [h_dir]
    exact h_z'_eq
  have h_dist : dist (c • x) (c • (T.base + t • T.direction)) ≤ c * δ := by
    have h1 : dist (c • x) (c • (T.base + t • T.direction)) = c * dist x (T.base + t • T.direction) := by
      rw [dist_eq_norm, dist_eq_norm]
      have h2 : ‖c • x - c • (T.base + t • T.direction)‖ = c * ‖x - (T.base + t • T.direction)‖ := by
        have h3 : c • x - c • (T.base + t • T.direction) = c • (x - (T.base + t • T.direction)) := by
          rw [smul_sub]
        rw [h3, norm_smul]
        have h4 : ‖c‖ = c := abs_of_pos hc
        rw [h4] <;> ring
      exact h2
    rw [h1]
    have h3 : dist x (T.base + t • T.direction) ≤ δ := by
      simpa [Metric.mem_closedBall, dist_eq_norm, hz_eq] using hxz
    exact mul_le_mul_of_nonneg_left h3 (by linarith)
  exact Metric.mem_cthickening_of_dist_le (c • x) (c • (T.base + t • T.direction)) (c * δ)
    (Kakeya.unitSegment (normalizeDeltaTube T c).base (normalizeDeltaTube T c).direction)
    h_z'_in_seg h_dist

end Kakeya.Assouad
