import MyLeanRepo.Kakeya.Streamlined.Geometry
import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Streamlined.Estimates
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Rigid motions of tube families

A rigid motion is a linear isometry (rotation/reflection) followed by a
translation. This module defines rigid motions of tubes, tube families,
body families, and shadings, and proves preservation of volume, essential
distinctness, density, deltaMax, and Frostman constants.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

variable (e : Point3 ≃ₗᵢ[ℝ] Point3) (t : Point3)

/-- The affine map `x ↦ e x + t`. -/
def rigidMoveMap (x : Point3) : Point3 :=
  e x + t

/-- The inverse affine map `y ↦ e.symm (y - t)`. -/
def rigidMoveInv (y : Point3) : Point3 :=
  e.symm (y - t)

lemma rigidMove_left_inv : ∀ x, rigidMoveInv e t (rigidMoveMap e t x) = x := by
  intro x
  simp [rigidMoveMap, rigidMoveInv]

lemma rigidMove_right_inv : ∀ y, rigidMoveMap e t (rigidMoveInv e t y) = y := by
  intro y
  simp [rigidMoveMap, rigidMoveInv]

/-- The rigid motion map is an isometry. -/
lemma rigidMoveMap_isometry : Isometry (rigidMoveMap e t) := by
  intro x y
  have h : edist (rigidMoveMap e t x) (rigidMoveMap e t y) = edist (e x) (e y) := by
    simp [rigidMoveMap, edist_dist]
  rw [h]
  exact e.isometry x y

/-- The inverse rigid motion is also an isometry. -/
lemma rigidMoveInv_isometry : Isometry (rigidMoveInv e t) := by
  intro x y
  have h : edist (rigidMoveInv e t x) (rigidMoveInv e t y) = edist (e.symm x) (e.symm y) := by
    simp [rigidMoveInv, edist_dist]
  rw [h]
  exact e.symm.isometry x y

/-- The rigid motion map as a homeomorphism. -/
def rigidMoveEquiv : Point3 ≃ₜ Point3 :=
  { toFun := rigidMoveMap e t
    invFun := rigidMoveInv e t
    left_inv := rigidMove_left_inv e t
    right_inv := rigidMove_right_inv e t
    continuous_toFun := by
      have h : Continuous (fun x : Point3 => e x + t) := by fun_prop
      exact h
    continuous_invFun := by
      have h : Continuous (fun y : Point3 => e.symm (y - t)) := by fun_prop
      exact h }

/-- The rigid motion as an affine map. -/
def rigidMoveAffineMap : Point3 →ᵃ[ℝ] Point3 :=
  { toFun := rigidMoveMap e t
    linear := (e : Point3 →ₗ[ℝ] Point3)
    map_vadd' := by
      intro p v
      simp [rigidMoveMap, vadd_eq_add]
      <;> abel }

/-- The rigid motion map preserves Lebesgue measure. -/
lemma rigidMoveMap_measurePreserving :
    MeasurePreserving (rigidMoveMap e t) volume volume := by
  have h1 : MeasurePreserving e volume volume := e.measurePreserving
  have h2 : MeasurePreserving (fun x : Point3 => x + t) volume volume :=
    measurePreserving_add_right volume t
  exact h2.comp h1

/-- The inverse rigid motion map preserves Lebesgue measure. -/
lemma rigidMoveInv_measurePreserving :
    MeasurePreserving (rigidMoveInv e t) volume volume := by
  have h1 : MeasurePreserving (fun y : Point3 => y - t) volume volume :=
    measurePreserving_add_right volume (-t)
  have h2 : MeasurePreserving e.symm volume volume := e.symm.measurePreserving
  exact h2.comp h1

/-- Image of a set under the rigid motion equals preimage under inverse. -/
lemma rigidMove_image (s : Set Point3) :
    rigidMoveMap e t '' s = (rigidMoveInv e t) ⁻¹' s := by
  ext z
  simp only [Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h_goal : rigidMoveInv e t (rigidMoveMap e t x) ∈ s := by
      rw [rigidMove_left_inv e t x]
      exact hx
    exact h_goal
  · intro hz
    refine ⟨rigidMoveInv e t z, hz, ?_⟩
    exact rigidMove_right_inv e t z

/-- Volume of image equals volume of original for null-measurable sets. -/
lemma rigidMove_volume {s : Set Point3} (hs : NullMeasurableSet s volume) :
    volume (rigidMoveMap e t '' s) = volume s := by
  have h_image_eq : rigidMoveMap e t '' s = (rigidMoveInv e t) ⁻¹' s :=
    rigidMove_image e t s
  rw [h_image_eq]
  exact (rigidMoveInv_measurePreserving e t).measure_preimage hs

/-- Convexity is preserved under rigid motion. -/
lemma rigidMove_convex {s : Set Point3} (hs : Convex ℝ s) :
    Convex ℝ (rigidMoveMap e t '' s) :=
  Convex.affine_image (rigidMoveAffineMap e t) hs

/-- Image of inverse-image equals original. -/
lemma rigidMove_image_inv (s : Set Point3) :
    rigidMoveMap e t '' (rigidMoveInv e t '' s) = s := by
  have h_comp : (rigidMoveMap e t) ∘ (rigidMoveInv e t) = id := by
    funext x
    exact rigidMove_right_inv e t x
  have h : rigidMoveMap e t '' (rigidMoveInv e t '' s) =
      ((rigidMoveMap e t) ∘ (rigidMoveInv e t)) '' s := by
    ext z
    simp [Set.mem_image]
  rw [h, h_comp]
  simp

/-- Inverse-image of image equals original. -/
lemma rigidMove_inv_image (s : Set Point3) :
    rigidMoveInv e t '' (rigidMoveMap e t '' s) = s := by
  have h_comp : (rigidMoveInv e t) ∘ (rigidMoveMap e t) = id := by
    funext x
    exact rigidMove_left_inv e t x
  have h : rigidMoveInv e t '' (rigidMoveMap e t '' s) =
      ((rigidMoveInv e t) ∘ (rigidMoveMap e t)) '' s := by
    ext z
    simp [Set.mem_image]
  rw [h, h_comp]
  simp

/-- Cthickening commutes with rigid motion. -/
lemma rigidMove_cthickening (r : ℝ) (s : Set Point3) :
    rigidMoveMap e t '' Metric.cthickening r s =
    Metric.cthickening r (rigidMoveMap e t '' s) := by
  let f := rigidMoveMap e t
  have h_f_isom : Isometry f := rigidMoveMap_isometry e t
  ext z
  simp only [Set.mem_image, Metric.mem_cthickening_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h_inf : Metric.infEDist (f x) (f '' s) ≤ ENNReal.ofReal r := by
      have h : Metric.infEDist (f x) (f '' s) = Metric.infEDist x s :=
        Metric.infEDist_image (hΦ := h_f_isom)
      rw [h]
      exact hx
    exact h_inf
  · intro hz
    refine ⟨rigidMoveInv e t z, ?_, ?_⟩
    · have h : Metric.infEDist (f (rigidMoveInv e t z)) (f '' s) =
          Metric.infEDist (rigidMoveInv e t z) s :=
        Metric.infEDist_image (hΦ := h_f_isom)
      have h2 : f (rigidMoveInv e t z) = z := rigidMove_right_inv e t z
      rw [h2] at h
      rw [←h]
      exact hz
    · exact rigidMove_right_inv e t z

/-! ### Rigid motion of tubes -/

variable {e t}

/-- Apply a rigid motion (linear isometry + translation) to a δ-tube. -/
def rigidMoveTube {δ : ℝ} (T : Kakeya.DeltaTube δ)
    (e : Point3 ≃ₗᵢ[ℝ] Point3) (t : Point3) : Kakeya.DeltaTube δ :=
  { base := e T.base + t
    direction := e T.direction
    direction_unit := by
      have h : ‖e T.direction‖ = ‖T.direction‖ := e.norm_map T.direction
      rw [h, T.direction_unit] }

/-- The carrier of a rigidly moved tube is the image of the original carrier. -/
lemma rigidMoveTube_carrier {δ : ℝ} (T : Kakeya.DeltaTube δ)
    (e : Point3 ≃ₗᵢ[ℝ] Point3) (t : Point3) :
    (rigidMoveTube T e t).carrier = rigidMoveMap e t '' T.carrier := by
  let f := rigidMoveMap e t
  have h_lin : ∀ (s : ℝ), f (T.base + s • T.direction) =
      (e T.base + t) + s • (e T.direction) := by
    intro s
    simp [f, rigidMoveMap]
    <;> abel
  have h_seg : f '' Kakeya.unitSegment T.base T.direction =
      Kakeya.unitSegment (e T.base + t) (e T.direction) := by
    dsimp only [Kakeya.unitSegment]
    rw [Set.image_image]
    apply Set.image_congr
    intro x _
    exact h_lin x
  simp only [rigidMoveTube, Kakeya.DeltaTube.carrier]
  rw [rigidMove_cthickening e t δ (Kakeya.unitSegment T.base T.direction), h_seg]

/-- Rigid motion preserves tube volume. -/
lemma rigidMoveTube_volume {δ : ℝ} (T : Kakeya.DeltaTube δ)
    (e : Point3 ≃ₗᵢ[ℝ] Point3) (t : Point3) :
    (rigidMoveTube T e t).volume = T.volume := by
  rw [Kakeya.DeltaTube.volume, rigidMoveTube_carrier T e t, Kakeya.DeltaTube.volume]
  have h_meas : MeasurableSet T.carrier :=
    Metric.isClosed_cthickening.measurableSet
  exact rigidMove_volume e t h_meas.nullMeasurableSet

/-- Rigid motion preserves essential distinctness. -/
lemma rigidMoveTube_essentiallyDistinct {δ : ℝ}
    (T U : Kakeya.DeltaTube δ)
    (e : Point3 ≃ₗᵢ[ℝ] Point3) (t : Point3) :
    T.EssentiallyDistinct U ↔
    (rigidMoveTube T e t).EssentiallyDistinct (rigidMoveTube U e t) := by
  simp only [Kakeya.DeltaTube.EssentiallyDistinct]
  let f := rigidMoveMap e t
  have h_inj : Function.Injective f := (rigidMoveEquiv e t).injective
  have h_inter_img : f '' (T.carrier ∩ U.carrier) =
      (f '' T.carrier) ∩ (f '' U.carrier) := by
    ext z
    simp only [Set.mem_image, Set.mem_inter_iff]
    constructor
    · rintro ⟨x, ⟨hxT, hxU⟩, rfl⟩
      exact ⟨⟨x, hxT, rfl⟩, ⟨x, hxU, rfl⟩⟩
    · rintro ⟨⟨x, hxT, rfl⟩, ⟨y, hyU, h_eq⟩⟩
      have hxy : x = y := h_inj h_eq.symm
      have hyU' : x ∈ U.carrier := by exact hxy ▸ hyU
      exact ⟨x, ⟨hxT, hyU'⟩, rfl⟩
  have h_inter : (rigidMoveTube T e t).carrier ∩ (rigidMoveTube U e t).carrier =
      f '' (T.carrier ∩ U.carrier) := by
    rw [rigidMoveTube_carrier T e t, rigidMoveTube_carrier U e t]
    exact h_inter_img.symm
  have h_meas : MeasurableSet (T.carrier ∩ U.carrier) :=
    Metric.isClosed_cthickening.measurableSet.inter Metric.isClosed_cthickening.measurableSet
  have h_vol_inter : volume ((rigidMoveTube T e t).carrier ∩ (rigidMoveTube U e t).carrier) =
      volume (T.carrier ∩ U.carrier) := by
    rw [h_inter]
    exact rigidMove_volume e t h_meas.nullMeasurableSet
  have h_volT : (rigidMoveTube T e t).volume = T.volume :=
    rigidMoveTube_volume T e t
  have h_volU : (rigidMoveTube U e t).volume = U.volume :=
    rigidMoveTube_volume U e t
  rw [h_vol_inter, h_volT, h_volU]

/-! ### Rigid motion of body families -/

/-- Apply a rigid motion to a body. -/
def rigidMoveBody (B : Body) (e : Point3 ≃ₗᵢ[ℝ] Point3) (t : Point3) : Body :=
  ⟨rigidMoveMap e t '' B.carrier⟩

/-- Rigid motion preserves body volume (measurable carrier). -/
lemma rigidMoveBody_volume (B : Body)
    (e : Point3 ≃ₗᵢ[ℝ] Point3) (t : Point3)
    (h_meas : MeasurableSet B.carrier) :
    (rigidMoveBody B e t).volume = B.volume :=
  rigidMove_volume e t h_meas.nullMeasurableSet

/-- Apply a rigid motion to a body family. -/
def rigidMoveBodyFamily (F : BodyFamily)
    (e : Point3 ≃ₗᵢ[ℝ] Point3) (t : Point3) : BodyFamily where
  card := F.card
  body i := rigidMoveBody (F.body i) e t

/-- Rigid motion preserves total mass. -/
lemma rigidMoveBodyFamily_mass (F : BodyFamily)
    (e : Point3 ≃ₗᵢ[ℝ] Point3) (t : Point3)
    (h_meas : ∀ i, MeasurableSet (F.body i).carrier) :
    (rigidMoveBodyFamily F e t).mass = F.mass := by
  dsimp only [rigidMoveBodyFamily, BodyFamily.mass]
  apply Finset.sum_congr rfl
  intro i _
  exact rigidMoveBody_volume (F.body i) e t (h_meas i)

/-- Rigid motion preserves density on image sets. -/
lemma rigidMoveBodyFamily_density (F : BodyFamily)
    (e : Point3 ≃ₗᵢ[ℝ] Point3) (t : Point3)
    {K : Set Point3} (hK : NullMeasurableSet K volume)
    (h_meas : ∀ i, MeasurableSet (F.body i).carrier) :
    (rigidMoveBodyFamily F e t).density (rigidMoveMap e t '' K) = F.density K := by
  dsimp only [BodyFamily.density]
  let f := rigidMoveMap e t
  have h_inj : Function.Injective f := (rigidMoveEquiv e t).injective
  have h_contained : ∀ i,
      ((rigidMoveBody (F.body i) e t).carrier ⊆ f '' K) ↔
      (F.body i).carrier ⊆ K := by
    intro i
    constructor
    · intro h
      exact (Set.image_subset_image_iff h_inj).mp h
    · intro h
      exact Set.image_mono h
  have h_indices_eq : (rigidMoveBodyFamily F e t).containedIndices (f '' K) =
      F.containedIndices K := by
    classical
    dsimp only [rigidMoveBodyFamily, BodyFamily.containedIndices]
    apply Finset.filter_congr
    intro i _
    exact h_contained i
  have h_containedMass : (rigidMoveBodyFamily F e t).containedMass (f '' K) =
      F.containedMass K := by
    dsimp only [BodyFamily.containedMass]
    rw [h_indices_eq]
    apply Finset.sum_congr rfl
    intro i _
    exact rigidMoveBody_volume (F.body i) e t (h_meas i)
  have h_vol : volume (f '' K) = volume K := rigidMove_volume e t hK
  rw [h_containedMass, h_vol]

/-- Rigid motion preserves deltaMax. -/
lemma rigidMoveBodyFamily_deltaMax (F : BodyFamily)
    (e : Point3 ≃ₗᵢ[ℝ] Point3) (t : Point3)
    (h_meas : ∀ i, MeasurableSet (F.body i).carrier) :
    (rigidMoveBodyFamily F e t).deltaMax = F.deltaMax := by
  let f := rigidMoveMap e t
  let g := rigidMoveInv e t
  have h_g_affine : ∀ (s : Set Point3), Convex ℝ s → Convex ℝ (g '' s) := by
    intro s hs
    let g_affine : Point3 →ᵃ[ℝ] Point3 :=
      { toFun := g
        linear := (e.symm : Point3 →ₗ[ℝ] Point3)
        map_vadd' := by
          intro p v
          simp [g, rigidMoveInv, vadd_eq_add] <;> abel }
    exact Convex.affine_image g_affine hs
  have h_main : ∀ (d : ENNReal),
      (∃ (K : Set Point3), Convex ℝ K ∧ d = (rigidMoveBodyFamily F e t).density K) ↔
      (∃ (K : Set Point3), Convex ℝ K ∧ d = F.density K) := by
    intro d
    constructor
    · rintro ⟨K, hK_conv, rfl⟩
      let K' := g '' K
      have hK'_conv : Convex ℝ K' := h_g_affine K hK_conv
      have hK'_null : NullMeasurableSet K' volume :=
        Convex.nullMeasurableSet volume hK'_conv
      have h_img : f '' K' = K := rigidMove_image_inv e t K
      have h_dens : (rigidMoveBodyFamily F e t).density K = F.density K' := by
        rw [←h_img]
        exact rigidMoveBodyFamily_density F e t hK'_null h_meas
      exact ⟨K', hK'_conv, h_dens⟩
    · rintro ⟨K, hK_conv, rfl⟩
      let K' := f '' K
      have hK'_conv : Convex ℝ K' := rigidMove_convex e t hK_conv
      have hK_null : NullMeasurableSet K volume :=
        Convex.nullMeasurableSet volume hK_conv
      have h_dens2 : (rigidMoveBodyFamily F e t).density K' = F.density K :=
        rigidMoveBodyFamily_density F e t hK_null h_meas
      exact ⟨K', hK'_conv, h_dens2.symm⟩
  have h_set_eq : {d : ENNReal | ∃ (K : Set Point3), Convex ℝ K ∧
      d = (rigidMoveBodyFamily F e t).density K} =
      {d : ENNReal | ∃ (K : Set Point3), Convex ℝ K ∧ d = F.density K} := by
    ext d
    exact h_main d
  rw [BodyFamily.deltaMax, h_set_eq]
  <;> rfl

/-- Rigid motion preserves frostmanConstantIn. -/
lemma rigidMoveBodyFamily_frostmanConstantIn (F : BodyFamily)
    (e : Point3 ≃ₗᵢ[ℝ] Point3) (t : Point3) (U : Set Point3)
    (hU : NullMeasurableSet U volume)
    (h_meas : ∀ i, MeasurableSet (F.body i).carrier) :
    (rigidMoveBodyFamily F e t).frostmanConstantIn (rigidMoveMap e t '' U) =
    F.frostmanConstantIn U := by
  let f := rigidMoveMap e t
  let g := rigidMoveInv e t
  have h_g_affine : ∀ (s : Set Point3), Convex ℝ s → Convex ℝ (g '' s) := by
    intro s hs
    let g_affine : Point3 →ᵃ[ℝ] Point3 :=
      { toFun := g
        linear := (e.symm : Point3 →ₗ[ℝ] Point3)
        map_vadd' := by
          intro p v
          simp [g, rigidMoveInv, vadd_eq_add] <;> abel }
    exact Convex.affine_image g_affine hs
  have h_densU : (rigidMoveBodyFamily F e t).density (f '' U) = F.density U :=
    rigidMoveBodyFamily_density F e t hU h_meas
  have h_main : ∀ (c : ENNReal),
      (∃ (K : Set Point3), Convex ℝ K ∧ K ⊆ f '' U ∧
        c = (rigidMoveBodyFamily F e t).density K /
          (rigidMoveBodyFamily F e t).density (f '' U)) ↔
      (∃ (K : Set Point3), Convex ℝ K ∧ K ⊆ U ∧
        c = F.density K / F.density U) := by
    intro c
    constructor
    · rintro ⟨K, hK_conv, hK_sub, rfl⟩
      let K' := g '' K
      have hK'_conv : Convex ℝ K' := h_g_affine K hK_conv
      have h_img : f '' K' = K := rigidMove_image_inv e t K
      have hK'_sub : K' ⊆ U := by
        have h : f '' K' ⊆ f '' U := by rw [h_img]; exact hK_sub
        exact (Set.image_subset_image_iff (rigidMoveEquiv e t).injective).mp h
      have hK'_null : NullMeasurableSet K' volume :=
        Convex.nullMeasurableSet volume hK'_conv
      have h_densK : (rigidMoveBodyFamily F e t).density K = F.density K' := by
        rw [←h_img]
        exact rigidMoveBodyFamily_density F e t hK'_null h_meas
      have h_eq : (rigidMoveBodyFamily F e t).density K /
            (rigidMoveBodyFamily F e t).density (f '' U) =
          F.density K' / F.density U := by
        rw [h_densK, h_densU]
      exact ⟨K', hK'_conv, hK'_sub, h_eq⟩
    · rintro ⟨K, hK_conv, hK_sub, rfl⟩
      let K' := f '' K
      have hK'_conv : Convex ℝ K' := rigidMove_convex e t hK_conv
      have hK'_sub : K' ⊆ f '' U := Set.image_mono hK_sub
      have hK_null : NullMeasurableSet K volume :=
        Convex.nullMeasurableSet volume hK_conv
      have h_densK : (rigidMoveBodyFamily F e t).density K' = F.density K :=
        rigidMoveBodyFamily_density F e t hK_null h_meas
      have h_eq : F.density K / F.density U =
          (rigidMoveBodyFamily F e t).density K' /
            (rigidMoveBodyFamily F e t).density (f '' U) := by
        rw [h_densK.symm, h_densU.symm]
      exact ⟨K', hK'_conv, hK'_sub, h_eq⟩
  have h_set_eq : {c : ENNReal | ∃ (K : Set Point3), Convex ℝ K ∧
        K ⊆ f '' U ∧
        c = (rigidMoveBodyFamily F e t).density K /
          (rigidMoveBodyFamily F e t).density (f '' U)} =
      {c : ENNReal | ∃ (K : Set Point3), Convex ℝ K ∧ K ⊆ U ∧
        c = F.density K / F.density U} := by
    ext c
    exact h_main c
  rw [BodyFamily.frostmanConstantIn, h_set_eq]
  <;> rfl

/-! ### Rigid motion of tube families -/

/-- Apply a rigid motion to all tubes in a tube family. -/
def rigidMoveFamily {δ : ℝ} (F : TubeFamily δ)
    (e : Point3 ≃ₗᵢ[ℝ] Point3) (t : Point3) : TubeFamily δ where
  card := F.card
  tube i := rigidMoveTube (F.tube i) e t

/-- All tube bodies have measurable carriers. -/
lemma tubeFamily_bodies_measurable {δ : ℝ} (F : TubeFamily δ) :
    ∀ i, MeasurableSet (F.toBodyFamily.body i).carrier := by
  intro i
  exact Metric.isClosed_cthickening.measurableSet

/-- Rigid motion preserves IsInUnitBall when motion maps unit ball into itself. -/
lemma rigidMoveFamily_preserves_unitBall {δ : ℝ} (F : TubeFamily δ)
    (e : Point3 ≃ₗᵢ[ℝ] Point3) (t : Point3)
    (h_maps_ball : rigidMoveMap e t '' Kakeya.DeltaTube.unitBall ⊆ Kakeya.DeltaTube.unitBall)
    (hF : F.IsInUnitBall) :
    (rigidMoveFamily F e t).IsInUnitBall := by
  intro i
  have h1 : (F.tube i).carrier ⊆ Kakeya.DeltaTube.unitBall := by
    have h := hF i
    simpa [Kakeya.DeltaTube.IsInUnitBall] using h
  have h2 : (rigidMoveTube (F.tube i) e t).carrier =
      rigidMoveMap e t '' (F.tube i).carrier :=
    rigidMoveTube_carrier (F.tube i) e t
  have h3 : (rigidMoveTube (F.tube i) e t).carrier ⊆ Kakeya.DeltaTube.unitBall := by
    rw [h2]
    exact (Set.image_mono h1).trans h_maps_ball
  simpa [TubeFamily.IsInUnitBall, rigidMoveFamily, Kakeya.DeltaTube.IsInUnitBall] using h3

/-- Rigid motion preserves essential distinctness of a tube family. -/
lemma rigidMoveFamily_preserves_distinct {δ : ℝ} (F : TubeFamily δ)
    (e : Point3 ≃ₗᵢ[ℝ] Point3) (t : Point3) :
    F.IsEssentiallyDistinct → (rigidMoveFamily F e t).IsEssentiallyDistinct := by
  intro hF
  intro i j hne
  have h_orig := hF i j hne
  exact (rigidMoveTube_essentiallyDistinct (F.tube i) (F.tube j) e t).mp h_orig

/-- Rigid motion preserves Nonempty. -/
lemma rigidMoveFamily_nonempty {δ : ℝ} (F : TubeFamily δ)
    (e : Point3 ≃ₗᵢ[ℝ] Point3) (t : Point3) :
    F.Nonempty → (rigidMoveFamily F e t).Nonempty := by
  intro h
  exact h

/-! ### Rigid motion of shadings -/

/-- Apply a rigid motion to a shading. -/
def rigidMoveShading {F : BodyFamily} (Y : Shading F)
    (e : Point3 ≃ₗᵢ[ℝ] Point3) (t : Point3) :
    Shading (rigidMoveBodyFamily F e t) where
  carrier i := rigidMoveMap e t '' Y.carrier i
  measurable_carrier i := by
    have h_image_eq : rigidMoveMap e t '' Y.carrier i =
        (rigidMoveInv e t) ⁻¹' Y.carrier i := rigidMove_image e t (Y.carrier i)
    rw [h_image_eq]
    exact (Y.measurable_carrier i).preimage (rigidMoveEquiv e t).continuous_invFun.measurable
  subset_body i := by
    have h : Y.carrier i ⊆ (F.body i).carrier := Y.subset_body i
    exact Set.image_mono h

/-- Rigid motion preserves shading mass. -/
lemma rigidMoveShading_mass {F : BodyFamily} (Y : Shading F)
    (e : Point3 ≃ₗᵢ[ℝ] Point3) (t : Point3) :
    (rigidMoveShading Y e t).mass = Y.mass := by
  dsimp only [rigidMoveShading, Shading.mass]
  apply Finset.sum_congr rfl
  intro i _
  exact rigidMove_volume e t (Y.measurable_carrier i).nullMeasurableSet

/-- Rigid motion preserves lambda density. -/
lemma rigidMoveShading_density {F : BodyFamily} (Y : Shading F)
    (e : Point3 ≃ₗᵢ[ℝ] Point3) (t : Point3) (lambda : ENNReal)
    (h_meas : ∀ i, MeasurableSet (F.body i).carrier) :
    Y.IsLambdaDense lambda → (rigidMoveShading Y e t).IsLambdaDense lambda := by
  intro h
  dsimp only [Shading.IsLambdaDense]
  have h1 : (rigidMoveBodyFamily F e t).mass = F.mass :=
    rigidMoveBodyFamily_mass F e t h_meas
  have h2 : (rigidMoveShading Y e t).mass = Y.mass :=
    rigidMoveShading_mass Y e t
  rw [h1, h2]
  exact h

/-- Rigid motion preserves average multiplicity bound. -/
lemma rigidMoveShading_multiplicity {F : BodyFamily} (Y : Shading F)
    (e : Point3 ≃ₗᵢ[ℝ] Point3) (t : Point3) (M : ENNReal) :
    Y.HasAverageMultiplicityAtMost M →
    (rigidMoveShading Y e t).HasAverageMultiplicityAtMost M := by
  intro h
  dsimp only [Shading.HasAverageMultiplicityAtMost]
  let f := rigidMoveMap e t
  have h_mass : (rigidMoveShading Y e t).mass = Y.mass :=
    rigidMoveShading_mass Y e t
  have h_union : (rigidMoveShading Y e t).union = f '' Y.union := by
    ext z
    simp [Shading.union, rigidMoveShading, Set.mem_image]
    <;> aesop
  have h_vol : volume ((rigidMoveShading Y e t).union) = volume Y.union := by
    rw [h_union]
    have h_meas : MeasurableSet Y.union := by
      have h_union_def : Y.union = ⋃ (i : Fin F.card), Y.carrier i := by
        ext x
        simp [Shading.union]
      rw [h_union_def]
      exact MeasurableSet.iUnion (fun i => Y.measurable_carrier i)
    exact rigidMove_volume e t h_meas.nullMeasurableSet
  rw [h_mass, h_vol]
  exact h

end Kakeya.Streamlined
