import MyLeanRepo.Kakeya.Assouad.WZ1.GlobalPlaninessTransportStatements
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Horizontal chart normalization for WZ1 Proposition 9

Transport the complete coherent tube configuration through the coordinate
permutation selected by `WZ1HorizontalChart`.  For `.first` this is the
identity; for `.second` it swaps coordinates `0` and `1` everywhere.
-/

noncomputable section

namespace Kakeya.Assouad

open Kakeya.Streamlined MeasureTheory Set Metric

-- ============================================================================
-- 1. Chart isometry
-- ============================================================================

/-- Linear isometry swapping coordinates `0` and `1`. -/
def wz1Swap01 : Point3 ≃ₗᵢ[ℝ] Point3 :=
  LinearIsometryEquiv.piLpCongrLeft (2 : ENNReal) ℝ ℝ (Equiv.swap (0 : Fin 3) 1)

lemma wz1Swap01_apply (p : Point3) :
    wz1Swap01 p = point3 (p 1) (p 0) (p 2) := by
  ext k
  fin_cases k <;> simp [wz1Swap01, LinearIsometryEquiv.piLpCongrLeft_apply,
    point3, PiLp.single_apply] <;> aesop

lemma wz1Swap01_involutive (p : Point3) :
    wz1Swap01 (wz1Swap01 p) = p := by
  ext k
  fin_cases k <;> simp [wz1Swap01, LinearIsometryEquiv.piLpCongrLeft_apply] <;> aesop

namespace WZ1HorizontalChart

/-- The chart map as a linear isometry equivalence. -/
def isometry (chart : WZ1HorizontalChart) : Point3 ≃ₗᵢ[ℝ] Point3 :=
  match chart with
  | .first => LinearIsometryEquiv.refl ℝ Point3
  | .second => wz1Swap01

lemma isometry_apply (chart : WZ1HorizontalChart) (p : Point3) :
    chart.isometry p = chart.mapPoint p := by
  cases chart <;> simp [isometry, mapPoint, wz1Swap01_apply] <;> rfl

lemma isometry_involutive (chart : WZ1HorizontalChart) (p : Point3) :
    chart.isometry (chart.isometry p) = p := by
  cases chart <;> simp [isometry, wz1Swap01_involutive] <;> rfl

lemma isometry_preserves_coord2 (chart : WZ1HorizontalChart) (p : Point3) :
    (chart.isometry p) (2 : Fin 3) = p (2 : Fin 3) := by
  cases chart <;> simp [isometry, wz1Swap01_apply, point3, PiLp.single_apply] <;> aesop

lemma isometry_globalGrainDirection (chart : WZ1HorizontalChart) (m : ℝ) :
    chart.isometry (globalGrainDirection m) = chart.direction m := by
  cases chart
  · simp [isometry, direction, globalGrainDirection]
  · simp [isometry, direction, globalGrainDirection, wz1Swap01_apply,
      point3, PiLp.single_apply]
    <;> ext k <;> fin_cases k <;> simp <;> aesop

end WZ1HorizontalChart

-- ============================================================================
-- 2. Generic transport helpers
-- ============================================================================

/-- Volume of any set is preserved by a linear isometry. -/
lemma volume_image (e : Point3 ≃ₗᵢ[ℝ] Point3) :
    ∀ (s : Set Point3), volume (e '' s) = volume s := by
  let e_me : Point3 ≃ᵐ Point3 :=
    { toFun := e.symm
      invFun := e
      left_inv := e.symm.left_inv
      right_inv := e.symm.right_inv
      measurable_toFun := e.symm.continuous.measurable
      measurable_invFun := e.continuous.measurable }
  have hmp : MeasurePreserving e.symm volume volume := e.symm.measurePreserving
  intro s
  have h_eq : e '' s = e.symm ⁻¹' s := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have h : e.symm x = y := by
        rw [← hxy] <;> exact e.left_inv y
      rw [h] <;> exact hy
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  rw [h_eq]
  exact MeasurePreserving.measure_preimage_equiv (f := e_me) hmp s

/-- A linear isometry preserves metric thickenings. -/
lemma image_cthickening (e : Point3 ≃ₗᵢ[ℝ] Point3)
    {δ : ℝ} {s : Set Point3} :
    e '' Metric.cthickening δ s = Metric.cthickening δ (e '' s) := by
  ext y
  simp only [Metric.mem_cthickening_iff, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Metric.infEDist_image e.isometry]
    exact hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    have himage : e.symm '' (e '' s) = s := by
      rw [← Set.image_comp] <;> simp
    have hdist := Metric.infEDist_image e.symm.isometry (x := y) (t := e '' s)
    rw [himage] at hdist
    rw [hdist]; exact hy

/-- Image of unit segment under a linear isometry. -/
lemma image_unitSegment (e : Point3 ≃ₗᵢ[ℝ] Point3) (base direction : Point3) :
    e '' (unitSegment base direction) =
      unitSegment (e base) (e direction) := by
  have h : (fun t : ℝ => e (base + t • direction)) = (fun t : ℝ => e base + t • e direction) := by
    funext t
    rw [e.map_add, e.map_smul]
  simp only [unitSegment, Set.image_image, h]

-- ============================================================================
-- 3. Tube, family, shading transport
-- ============================================================================

/-- Transport a tube through a linear isometry. -/
def transportTube (e : Point3 ≃ₗᵢ[ℝ] Point3) {δ : ℝ}
    (T : Kakeya.DeltaTube δ) : Kakeya.DeltaTube δ where
  base := e T.base
  direction := e T.direction
  direction_unit := by
    have h : ‖e T.direction‖ = ‖T.direction‖ := e.norm_map T.direction
    rw [h, T.direction_unit]

lemma transportTube_carrier (e : Point3 ≃ₗᵢ[ℝ] Point3) {δ : ℝ}
    (T : Kakeya.DeltaTube δ) :
    (transportTube e T).carrier = e '' T.carrier := by
  have h1 : e '' T.carrier =
      Metric.cthickening δ (e '' (unitSegment T.base T.direction)) := by
    rw [Kakeya.DeltaTube.carrier]; exact image_cthickening e
  have h2 := image_unitSegment e T.base T.direction
  rw [h1, h2]; rfl

lemma transportTube_volume (e : Point3 ≃ₗᵢ[ℝ] Point3)
    (hvol : ∀ s, volume (e '' s) = volume s) {δ : ℝ} (T : Kakeya.DeltaTube δ) :
    (transportTube e T).volume = T.volume := by
  rw [Kakeya.DeltaTube.volume, Kakeya.DeltaTube.volume, transportTube_carrier e T, hvol T.carrier]

/-- Transport a tube family. -/
def transportFamily (e : Point3 ≃ₗᵢ[ℝ] Point3) {δ : ℝ}
    (F : Streamlined.TubeFamily δ) : Streamlined.TubeFamily δ where
  card := F.card
  tube i := transportTube e (F.tube i)

/-- Carrier equality after family transport. -/
lemma transportFamily_carrier (e : Point3 ≃ₗᵢ[ℝ] Point3) {δ : ℝ}
    (F : Streamlined.TubeFamily δ) (i : Fin F.card) :
    ((transportFamily e F).tube i).carrier = e '' (F.tube i).carrier :=
  transportTube_carrier e (F.tube i)

lemma transportFamily_toBody (e : Point3 ≃ₗᵢ[ℝ] Point3) {δ : ℝ}
    (F : Streamlined.TubeFamily δ) (i : Fin F.card) :
    ((transportFamily e F).toBodyFamily.body i).carrier =
      e '' (F.toBodyFamily.body i).carrier :=
  transportFamily_carrier e F i

lemma transportFamily_volume (e : Point3 ≃ₗᵢ[ℝ] Point3)
    (hvol : ∀ s, volume (e '' s) = volume s) {δ : ℝ}
    (F : Streamlined.TubeFamily δ) (i : Fin F.card) :
    ((transportFamily e F).toBodyFamily.body i).volume =
      (F.toBodyFamily.body i).volume := by
  have h : ((transportFamily e F).toBodyFamily.body i).carrier =
      e '' (F.toBodyFamily.body i).carrier := transportFamily_toBody e F i
  rw [Body.volume, h, Body.volume]
  exact hvol (F.toBodyFamily.body i).carrier

lemma transportFamily_mass (e : Point3 ≃ₗᵢ[ℝ] Point3)
    (hvol : ∀ s, volume (e '' s) = volume s) {δ : ℝ}
    (F : Streamlined.TubeFamily δ) :
    (transportFamily e F).toBodyFamily.mass = F.toBodyFamily.mass := by
  simp [BodyFamily.mass, transportFamily_volume e hvol F]
  <;> rfl

/-- Transport a shading. -/
def transportShading (e : Point3 ≃ₗᵢ[ℝ] Point3) {δ : ℝ}
    {F : Streamlined.TubeFamily δ}
    (Y : Streamlined.TubeShading F) :
    Streamlined.TubeShading (transportFamily e F) where
  carrier i := e '' Y.carrier i
  measurable_carrier i := by
    have hms : MeasurableSet (Y.carrier i) := Y.measurable_carrier i
    have h_eq : e '' Y.carrier i = e.symm ⁻¹' (Y.carrier i) := by
      ext x
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [e.left_inv] using hy
      · intro hx
        exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
    rw [h_eq]
    exact hms.preimage e.symm.continuous.measurable
  subset_body i := by
    have hsub : Y.carrier i ⊆ (F.toBodyFamily.body i).carrier := Y.subset_body i
    have hcar : ((transportFamily e F).toBodyFamily.body i).carrier =
        e '' (F.toBodyFamily.body i).carrier := transportFamily_toBody e F i
    rw [hcar]
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact ⟨x, hsub hx, rfl⟩

lemma transportShading_union (e : Point3 ≃ₗᵢ[ℝ] Point3) {δ : ℝ}
    {F : Streamlined.TubeFamily δ} {Y : Streamlined.TubeShading F} :
    (transportShading e Y).union = e '' Y.union := by
  ext x
  simp only [Shading.union, transportShading, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨i, y, hy, rfl⟩
    exact ⟨y, ⟨i, hy⟩, rfl⟩
  · rintro ⟨y, ⟨i, hy⟩, rfl⟩
    exact ⟨i, y, hy, rfl⟩

lemma transportShading_mass (e : Point3 ≃ₗᵢ[ℝ] Point3)
    (hvol : ∀ s, volume (e '' s) = volume s) {δ : ℝ}
    {F : Streamlined.TubeFamily δ} {Y : Streamlined.TubeShading F} :
    (transportShading e Y).mass = Y.mass := by
  simp only [Shading.mass, transportShading]
  apply Finset.sum_congr rfl
  intro i _
  exact hvol (Y.carrier i)


end Kakeya.Assouad
