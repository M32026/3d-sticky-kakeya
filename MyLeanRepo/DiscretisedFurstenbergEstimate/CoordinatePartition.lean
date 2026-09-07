module

/-
  Coordinate partition helpers for tube direction extraction.

  Splits a tube family into "flat" (|slope| ≤ 1, v1 ≠ 0) and "steep" (the rest).
  Swapping coordinates (x ↔ y) maps steep tubes to flat tubes.
  The swap map is an isometry on AffineLine, preserving S-set properties.

  Dependencies:
  - MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineParams
  - MyLeanRepo.DiscretisedFurstenbergEstimate.TubesAndSlopes
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineParams
public import MyLeanRepo.DiscretisedFurstenbergEstimate.TubesAndSlopes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.PackingBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HCommonWiring
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
open DirecretisedFurstenbergEstimate
open LemmaE
open DyadicCardToNcover

noncomputable section

namespace CoordinatePartition

/-- Coordinate swap on EuclideanPlane: (x,y) ↦ (y,x). -/
def swapCoords (p : EuclideanPlane) : EuclideanPlane :=
  WithLp.toLp 2 (fun i : Fin 2 => p (if i = 0 then 1 else 0))

/-- swapCoords is involutive. -/
lemma swapCoords_invol : Function.Involutive swapCoords := by
  intro x
  ext i
  fin_cases i <;> simp [swapCoords] <;> rfl

/-- swapCoords as a linear isometry equivalence. -/
def swapCoordsLI : EuclideanPlane ≃ₗᵢ[ℝ] EuclideanPlane :=
  { toFun := swapCoords
    invFun := swapCoords
    left_inv := swapCoords_invol
    right_inv := swapCoords_invol
    map_add' := by
      intro x y
      ext i
      fin_cases i <;> simp [swapCoords] <;> abel
    map_smul' := by
      intro c x
      ext i
      fin_cases i <;> simp [swapCoords] <;> ring
    norm_map' := by
      intro x
      have h : ‖swapCoords x‖ = ‖x‖ := by
        simp [swapCoords, EuclideanSpace.norm_eq, add_comm]
        <;> rfl
      exact h }

/-- swapCoords is an isometry. -/
lemma swapCoords_isometry : Isometry swapCoords :=
  swapCoordsLI.isometry

/-- Apply coordinate swap to an AffineLine. -/
def swapLine (ℓ : AffineLine) : AffineLine :=
  let f_af : EuclideanPlane →ᵃ[ℝ] EuclideanPlane := swapCoordsLI.toLinearEquiv.toAffineMap
  let img := AffineSubspace.map f_af ℓ.1
  have h_dir : img.direction = Submodule.map (swapCoordsLI.toLinearEquiv : EuclideanPlane →ₗ[ℝ] EuclideanPlane) ℓ.1.direction :=
    AffineSubspace.map_direction f_af ℓ.1
  have h_rank : Module.finrank ℝ img.direction = 1 := by
    rw [h_dir]
    have h_eq := LinearEquiv.finrank_map_eq swapCoordsLI.toLinearEquiv ℓ.1.direction
    rw [h_eq, ℓ.2]
  ⟨img, h_rank⟩

/-- The swapped line's underlying set is the image under swapCoords. -/
lemma swapLine_set_eq (ℓ : AffineLine) :
    ((swapLine ℓ).1 : Set EuclideanPlane) = swapCoords '' ℓ.1 := by
  rfl

/-- swapLine is involutive. -/
lemma swapLine_invol : Function.Involutive swapLine := by
  intro ℓ
  apply Subtype.ext
  have h_set_eq : ((swapLine (swapLine ℓ)).1 : Set EuclideanPlane) = (ℓ.1 : Set EuclideanPlane) := by
    calc
      ((swapLine (swapLine ℓ)).1 : Set EuclideanPlane)
        = swapCoords '' ((swapLine ℓ).1 : Set EuclideanPlane) := swapLine_set_eq (swapLine ℓ)
      _ = swapCoords '' (swapCoords '' (ℓ.1 : Set EuclideanPlane)) := by rw [swapLine_set_eq ℓ]
      _ = (ℓ.1 : Set EuclideanPlane) := by
        ext x
        simp only [Set.mem_image]
        constructor
        · rintro ⟨y, hy, rfl⟩
          rcases hy with ⟨z, hz, rfl⟩
          have h4 : swapCoords (swapCoords z) = z := swapCoords_invol z
          rw [h4]
          exact hz
        · intro hx
          exact ⟨swapCoords x, ⟨x, hx, rfl⟩, swapCoords_invol x⟩
  exact AffineSubspace.ext (Set.ext_iff.mp h_set_eq)

/-- External covering number is preserved by an involutive isometry. -/
lemma externalCoveringNumber_image_of_involutive_isometry
    {X : Type*} [EMetricSpace X] {f : X → X}
    (hf : Isometry f) (h_invol : Function.Involutive f)
    (ε : NNReal) (A : Set X) :
    Metric.externalCoveringNumber ε (f '' A) = Metric.externalCoveringNumber ε A := by
  have h_inj : Function.Injective f := hf.injective
  have h_main : ∀ (S : Set X), Metric.externalCoveringNumber ε (f '' S) ≤ Metric.externalCoveringNumber ε S := by
    intro S
    simp only [Metric.externalCoveringNumber]
    apply le_iInf_iff.mpr
    intro B
    apply le_iInf_iff.mpr
    intro hB
    have hB' : Metric.IsCover ε (f '' S) (f '' B) :=
      (hf.isCover_image_iff B).mpr hB
    have h_card : (f '' B).encard = B.encard := by
      exact Function.Injective.encard_image h_inj B
    have h : (⨅ (D : Set X) (_ : Metric.IsCover ε (f '' S) D), D.encard) ≤ (f '' B).encard :=
      iInf_le_of_le (f '' B) (iInf_le_of_le hB' le_rfl)
    rw [h_card] at h
    exact h
  have h1 := h_main A
  have h2 : f '' (f '' A) = A := by
    ext x
    simp only [Set.mem_image]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      have h5 := h_invol z
      rw [h5] at * <;> exact hz
    · intro hx
      exact ⟨f x, ⟨x, hx, rfl⟩, by exact h_invol x⟩
  have h3 := h_main (f '' A)
  rw [h2] at h3
  exact le_antisymm h1 h3

/-- swapLine is an isometry on AffineLine. -/
lemma swapLine_isometry : Isometry swapLine := by
  let f : EuclideanPlane ≃ₗᵢ[ℝ] EuclideanPlane := swapCoordsLI
  let fCLM : EuclideanPlane →L[ℝ] EuclideanPlane := f.toContinuousLinearMap
  let gCLM : EuclideanPlane →L[ℝ] EuclideanPlane := f.symm.toContinuousLinearMap
  have hf_norm : ‖fCLM‖ ≤ 1 := f.norm_toContinuousLinearMap.le
  have hg_norm : ‖gCLM‖ ≤ 1 := f.symm.norm_toContinuousLinearMap.le
  let f_af : EuclideanPlane →ᵃ[ℝ] EuclideanPlane := f.toLinearEquiv.toAffineMap

  have h_off : ∀ ℓ : AffineLine, (swapLine ℓ).offset = swapCoords ℓ.offset := by
    intro ℓ
    dsimp only [AffineLine.offset]
    let f_ai : EuclideanPlane →ᵃⁱ[ℝ] EuclideanPlane :=
      f.toAffineIsometryEquiv.toAffineIsometry
    have h_f0 : f_ai (0 : EuclideanPlane) = 0 := by exact Eq.symm (PiLp.ext (congrFun rfl))
    have h_fai : (f_ai : EuclideanPlane → EuclideanPlane) = swapCoords := by rfl
    have h_map : EuclideanGeometry.orthogonalProjection (AffineSubspace.map f_ai.toAffineMap ℓ.1) 0 =
        swapCoords (EuclideanGeometry.orthogonalProjection ℓ.1 0) := by
      have h1 := EuclideanGeometry.orthogonalProjection_map ℓ.1 f_ai (0 : EuclideanPlane)
      rw [h_f0] at h1
      rw [h_fai] at h1
      exact h1
    exact h_map

  have h_dir_map : ∀ (p : Submodule ℝ EuclideanPlane),
      (Submodule.map (f : EuclideanPlane →ₗ[ℝ] EuclideanPlane) p).starProjection =
      fCLM.comp (p.starProjection.comp gCLM) := by
    intro p
    apply ContinuousLinearMap.ext
    intro y
    have h1 : ∀ (z : EuclideanPlane),
        (Submodule.map (f : EuclideanPlane →ₗ[ℝ] EuclideanPlane) p).starProjection z =
        fCLM (p.starProjection (gCLM z)) := by
      intro z
      have h3 : fCLM (gCLM z) = z := by
        have h4 : f (f.symm z) = z := f.left_inv z
        exact h4
      have h5 : (Submodule.map (f : EuclideanPlane →ₗ[ℝ] EuclideanPlane) p).starProjection (fCLM (gCLM z)) =
          fCLM (p.starProjection (gCLM z)) := by
        have h6 : f (p.starProjection (gCLM z)) =
            (Submodule.map (f : EuclideanPlane →ₗ[ℝ] EuclideanPlane) p).starProjection (f (gCLM z)) :=
          LinearIsometry.map_starProjection' f.toLinearIsometry p (gCLM z)
        exact h6.symm
      rw [h3] at h5
      exact h5
    exact h1 y

  have h_norm_le : ∀ (a b : AffineLine),
      ‖(swapLine a).1.direction.starProjection - (swapLine b).1.direction.starProjection‖ ≤
      ‖a.1.direction.starProjection - b.1.direction.starProjection‖ := by
    intro a b
    let p := a.1.direction
    let q := b.1.direction
    have hp' : (swapLine a).1.direction = Submodule.map (f : EuclideanPlane →ₗ[ℝ] EuclideanPlane) p :=
      AffineSubspace.map_direction f_af a.1
    have hq' : (swapLine b).1.direction = Submodule.map (f : EuclideanPlane →ₗ[ℝ] EuclideanPlane) q :=
      AffineSubspace.map_direction f_af b.1
    rw [hp', hq']
    rw [h_dir_map p, h_dir_map q]
    have h : ‖fCLM.comp ((p.starProjection - q.starProjection).comp gCLM)‖ ≤
        ‖fCLM‖ * (‖p.starProjection - q.starProjection‖ * ‖gCLM‖) := by
      calc
        ‖fCLM.comp ((p.starProjection - q.starProjection).comp gCLM)‖
          ≤ ‖fCLM‖ * ‖(p.starProjection - q.starProjection).comp gCLM‖ := by exact ContinuousLinearMap.opNorm_comp_le fCLM ((p.starProjection - q.starProjection) ∘SL gCLM)
        _ ≤ ‖fCLM‖ * (‖p.starProjection - q.starProjection‖ * ‖gCLM‖) := by
          gcongr <;> exact ContinuousLinearMap.opNorm_comp_le (p.starProjection - q.starProjection) gCLM
    calc
      ‖fCLM.comp ((p.starProjection - q.starProjection).comp gCLM)‖
        ≤ ‖fCLM‖ * (‖p.starProjection - q.starProjection‖ * ‖gCLM‖) := h
      _ ≤ 1 * (‖p.starProjection - q.starProjection‖ * 1) := by gcongr <;> linarith
      _ = ‖p.starProjection - q.starProjection‖ := by ring

  have h_dist_eq : ∀ (a b : AffineLine), dist (swapLine a) (swapLine b) = dist a b := by
    intro a b
    have h1 : ‖(swapLine a).offset - (swapLine b).offset‖ = ‖a.offset - b.offset‖ := by
      rw [h_off a, h_off b]
      have h : dist (swapCoords a.offset) (swapCoords b.offset) = dist a.offset b.offset :=
        swapCoords_isometry.dist_eq a.offset b.offset
      simpa [dist_eq_norm] using h
    have h2 : ‖(swapLine a).1.direction.starProjection - (swapLine b).1.direction.starProjection‖ =
        ‖a.1.direction.starProjection - b.1.direction.starProjection‖ := by
      have h2a := h_norm_le a b
      have h2b := h_norm_le (swapLine a) (swapLine b)
      rw [swapLine_invol a, swapLine_invol b] at h2b
      linarith
    have h3 : dist (swapLine a) (swapLine b) =
        ‖(swapLine a).1.direction.starProjection - (swapLine b).1.direction.starProjection‖ +
        ‖(swapLine a).offset - (swapLine b).offset‖ := by
      rfl
    rw [h3, h2, h1] <;> rfl
  exact Isometry.of_dist_eq h_dist_eq

/-- swapLine preserves the S-set property. -/
lemma swapLine_sset {δ s C : ℝ} {T : Set AffineLine}
    (h : IsDeltaSSet δ s C T) :
    IsDeltaSSet δ s C (swapLine '' T) := by
  have h_iso : Isometry swapLine := swapLine_isometry
  rcases h with ⟨hne, hδ_pos, hC_pos, hs_nonneg, hmain⟩
  refine ⟨hne.image swapLine, hδ_pos, hC_pos, hs_nonneg, ?_⟩
  intro y r hr
  set x := swapLine y with hx_def
  have h_y_eq : y = swapLine x := by
    simp [hx_def, swapLine_invol]
    <;> exact (swapLine_invol y).symm
  rw [h_y_eq]
  have h_image_ball : (swapLine '' T) ∩ Metric.closedBall (swapLine x) r =
      swapLine '' (T ∩ Metric.closedBall x r) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_image]
    constructor
    · rintro ⟨⟨w, hw, rfl⟩, hz⟩
      refine ⟨w, ⟨hw, ?_⟩, rfl⟩
      have h_dist : dist (swapLine w) (swapLine x) ≤ r := hz
      have h_eq : dist (swapLine w) (swapLine x) = dist w x := h_iso.dist_eq w x
      rw [h_eq] at h_dist
      exact h_dist
    · rintro ⟨w, ⟨hw, hdist⟩, rfl⟩
      have h_ball : swapLine w ∈ Metric.closedBall (swapLine x) r := by
        simpa [Metric.mem_closedBall, h_iso.dist_eq w x] using hdist
      exact ⟨⟨w, hw, rfl⟩, h_ball⟩
  rw [h_image_ball]
  have h1 := externalCoveringNumber_image_of_involutive_isometry h_iso swapLine_invol δ.toNNReal (T ∩ Metric.closedBall x r)
  have h2 := externalCoveringNumber_image_of_involutive_isometry h_iso swapLine_invol δ.toNNReal T
  rw [h1, h2]
  exact hmain x r hr

/-- swapLine preserves near-thickening (with swapped point). -/
lemma swapLine_near {δ : ℝ} {p : EuclideanPlane} {ℓ : AffineLine}
    (h : p ∈ Metric.cthickening δ ℓ.1) :
    swapCoords p ∈ Metric.cthickening δ (swapLine ℓ).1 := by
  have h1 : Metric.infEDist p ℓ.1 ≤ ENNReal.ofReal δ := by
    simpa [Metric.mem_cthickening_iff] using h
  have h3 : ((swapLine ℓ).1 : Set EuclideanPlane) = swapCoords '' ℓ.1 := by
    rfl
  have h4 : Metric.infEDist (swapCoords p) ((swapLine ℓ).1 : Set EuclideanPlane) =
      Metric.infEDist p ℓ.1 := by
    rw [h3]
    exact Metric.infEDist_image swapCoords_isometry
  rw [Metric.mem_cthickening_iff, h4]
  exact h1

/-- Helper: direction submodule of finrank 1 equals span of any nonzero vector in it. -/
lemma direction_eq_span {p : Submodule ℝ EuclideanPlane} {v : EuclideanPlane}
    (hfin : Module.finrank ℝ p = 1) (hv : v ∈ p) (hvne : v ≠ 0) :
    p = ℝ ∙ v := by
  have h1 : ℝ ∙ v ≤ p := by
    rw [Submodule.span_singleton_le_iff_mem] <;> exact hv
  have h2 : Module.finrank ℝ (ℝ ∙ v) = 1 := finrank_span_singleton hvne
  have h3 : p ≤ ℝ ∙ v := by
    have h4 : Module.finrank ℝ p = Module.finrank ℝ (ℝ ∙ v) := by rw [hfin, h2]
    exact (Submodule.eq_of_le_of_finrank_eq h1 h4.symm).symm.le
  exact Submodule.eq_of_le_of_finrank_eq h3 (by rw [hfin, h2])

/-- If a line is "steep" (v1=0 or |slope|>1), its swap is "flat" (v1'≠0 and |slope'|≤1). -/
lemma steep_swap_flat (ℓ : AffineLine)
    (h_steep : (LemmaE.getDirV ℓ) 1 = 0 ∨ |(affineLineParams ℓ).1| > 1) :
    (LemmaE.getDirV (swapLine ℓ)) 1 ≠ 0 ∧
    |(affineLineParams (swapLine ℓ)).1| ≤ 1 := by
  let v := LemmaE.getDirV ℓ
  let v' := LemmaE.getDirV (swapLine ℓ)
  have hv_dir : v ∈ ℓ.1.direction := (LemmaE.getDirV_spec ℓ).1
  have hv_ne : v ≠ 0 := (LemmaE.getDirV_spec ℓ).2
  have hv'_dir : v' ∈ (swapLine ℓ).1.direction := (LemmaE.getDirV_spec (swapLine ℓ)).1
  have hv'_ne : v' ≠ 0 := (LemmaE.getDirV_spec (swapLine ℓ)).2
  let f_af : EuclideanPlane →ᵃ[ℝ] EuclideanPlane := swapCoordsLI.toLinearEquiv.toAffineMap
  have h_dir_eq : (swapLine ℓ).1.direction = Submodule.map (swapCoordsLI : EuclideanPlane →ₗ[ℝ] EuclideanPlane) ℓ.1.direction :=
    AffineSubspace.map_direction f_af ℓ.1
  have h_span : ℓ.1.direction = ℝ ∙ v := direction_eq_span ℓ.2 hv_dir hv_ne
  have h_span' : (swapLine ℓ).1.direction = ℝ ∙ swapCoords v := by
    rw [h_dir_eq, h_span]
    simp [Submodule.map_span]
    <;> rfl
  have h_exists : ∃ (c : ℝ), c ≠ 0 ∧ v' = c • swapCoords v := by
    have h6 : v' ∈ (swapLine ℓ).1.direction := hv'_dir
    rw [h_span'] at h6
    have h7 : v' ∈ Submodule.span ℝ {swapCoords v} := h6
    have h8 : ∃ (c : ℝ), c • swapCoords v = v' := by
      rw [Submodule.mem_span_singleton] at h7
      exact h7
    rcases h8 with ⟨c, hc⟩
    have hc' : v' = c • swapCoords v := hc.symm
    refine ⟨c, ?_, hc'⟩
    by_contra hc0
    rw [hc0, zero_smul] at hc
    exact hv'_ne hc.symm
  rcases h_exists with ⟨c, hc_ne, hvc⟩
  have h_v'1 : v' 1 = c * v 0 := by
    rw [hvc]
    simp [swapCoords] <;> rfl
  have h_v'0 : v' 0 = c * v 1 := by
    rw [hvc]
    simp [swapCoords] <;> rfl
  cases h_steep with
  | inl h_v1_eq_0 =>
    have h_v0_ne : v 0 ≠ 0 := by
      by_contra h
      have h_v_eq : v = 0 := by
        ext i
        fin_cases i <;> simp [h, h_v1_eq_0] <;> linarith
      exact hv_ne h_v_eq
    have h_v'1_ne : v' 1 ≠ 0 := by
      rw [h_v'1] <;> exact mul_ne_zero hc_ne h_v0_ne
    have h_a'_if : (affineLineParams (swapLine ℓ)).1 =
        if (getDirV (swapLine ℓ)) 1 = 0 then 0 else (getDirV (swapLine ℓ)) 0 / (getDirV (swapLine ℓ)) 1 := by
      simp [affineLineParams] <;> rfl
    have h_a' : (affineLineParams (swapLine ℓ)).1 = 0 := by
      rw [h_a'_if, if_neg h_v'1_ne]
      <;> rw [h_v'0, h_v1_eq_0] <;> ring
    exact ⟨h_v'1_ne, by rw [h_a'] <;> norm_num⟩
  | inr h_abs_gt_1 =>
    have h_v1_ne : v 1 ≠ 0 := by
      by_contra h
      have h_a_if : (affineLineParams ℓ).1 =
          if (getDirV ℓ) 1 = 0 then 0 else (getDirV ℓ) 0 / (getDirV ℓ) 1 := by
        simp [affineLineParams] <;> rfl
      have h_a_eq_0 : (affineLineParams ℓ).1 = 0 := by
        rw [h_a_if, if_pos h] <;> norm_num
      rw [h_a_eq_0] at h_abs_gt_1
      <;> norm_num at h_abs_gt_1 <;> linarith
    have h_a_if : (affineLineParams ℓ).1 =
        if (getDirV ℓ) 1 = 0 then 0 else (getDirV ℓ) 0 / (getDirV ℓ) 1 := by
      simp [affineLineParams] <;> rfl
    have h_a_eq : (affineLineParams ℓ).1 = v 0 / v 1 := by
      rw [h_a_if, if_neg h_v1_ne] <;> rfl
    have h_v0_ne : v 0 ≠ 0 := by
      by_contra h
      rw [h_a_eq, h, zero_div] at h_abs_gt_1
      <;> norm_num at h_abs_gt_1 <;> linarith
    have h_v'1_ne : v' 1 ≠ 0 := by
      rw [h_v'1] <;> exact mul_ne_zero hc_ne h_v0_ne
    have h_a'_if : (affineLineParams (swapLine ℓ)).1 =
        if (getDirV (swapLine ℓ)) 1 = 0 then 0 else (getDirV (swapLine ℓ)) 0 / (getDirV (swapLine ℓ)) 1 := by
      simp [affineLineParams] <;> rfl
    have h_a'_eq : (affineLineParams (swapLine ℓ)).1 = v' 0 / v' 1 := by
      rw [h_a'_if, if_neg h_v'1_ne] <;> rfl
    have h_final : (affineLineParams (swapLine ℓ)).1 = v 1 / v 0 := by
      rw [h_a'_eq, h_v'0, h_v'1]
      field_simp [hc_ne, h_v0_ne] <;> ring
    rw [h_final]
    have h_abs : |v 1 / v 0| ≤ 1 := by
      have h9 : |v 0 / v 1| > 1 := by
        rw [h_a_eq] at h_abs_gt_1 <;> exact h_abs_gt_1
      have h10 : |v 0| > |v 1| := by
        have h11 : |v 0 / v 1| = |v 0| / |v 1| := by rw [abs_div]
        rw [h11] at h9
        have h12 : 0 < |v 1| := abs_pos.mpr h_v1_ne
        calc
          |v 0| = (|v 0| / |v 1|) * |v 1| := by field_simp <;> ring
          _ > 1 * |v 1| := by gcongr
          _ = |v 1| := by ring
      have h13 : |v 1| ≤ |v 0| := by linarith
      have h14 : |v 1 / v 0| = |v 1| / |v 0| := by rw [abs_div]
      rw [h14]
      have h15 : 0 < |v 0| := abs_pos.mpr h_v0_ne
      exact (div_le_one h15).mpr h13
    exact ⟨h_v'1_ne, h_abs⟩

/-- Partition a finite tube family into flat and steep classes.
    One class has at least half the cardinality. -/
lemma partition_half {T : Finset AffineLine} [DecidableEq AffineLine] :
    ∃ (T_flat T_steep : Finset AffineLine),
      T_flat ∪ T_steep = T ∧
      Disjoint T_flat T_steep ∧
      (∀ ℓ ∈ T_flat, (LemmaE.getDirV ℓ) 1 ≠ 0 ∧ |(affineLineParams ℓ).1| ≤ 1) ∧
      (∀ ℓ ∈ T_steep, (LemmaE.getDirV ℓ) 1 = 0 ∨ |(affineLineParams ℓ).1| > 1) ∧
      (2 * T_flat.card ≥ T.card ∨ 2 * T_steep.card ≥ T.card) := by
  let is_flat : AffineLine → Prop := fun ℓ =>
    (LemmaE.getDirV ℓ) 1 ≠ 0 ∧ |(affineLineParams ℓ).1| ≤ 1
  let is_steep : AffineLine → Prop := fun ℓ =>
    (LemmaE.getDirV ℓ) 1 = 0 ∨ |(affineLineParams ℓ).1| > 1
  have h_not_flat_iff_steep : ∀ ℓ, ¬is_flat ℓ ↔ is_steep ℓ := by
    intro ℓ
    constructor
    · intro h
      by_cases h1 : (getDirV ℓ) 1 = 0
      · exact Or.inl h1
      · have h2 : |(affineLineParams ℓ).1| > 1 := by
          by_contra h3
          have h4 : |(affineLineParams ℓ).1| ≤ 1 := by linarith
          exact h ⟨h1, h4⟩
        exact Or.inr h2
    · rintro (h1 | h2)
      · intro h3
        exact h3.1 h1
      · intro h3
        linarith [h3.2]
  let T_flat : Finset AffineLine := T.filter (fun ℓ => is_flat ℓ)
  let T_steep : Finset AffineLine := T.filter (fun ℓ => is_steep ℓ)
  have h_disj : Disjoint T_flat T_steep := by
    rw [Finset.disjoint_left]
    intro ℓ h1 h2
    have hf : is_flat ℓ := (Finset.mem_filter.mp h1).2
    have hs : is_steep ℓ := (Finset.mem_filter.mp h2).2
    rcases hf with ⟨h_v1_ne, h_abs_le⟩
    rcases hs with (h_v1_eq | h_abs_gt)
    · exact h_v1_ne h_v1_eq
    · linarith
  have h_union : T_flat ∪ T_steep = T := by
    apply Finset.ext
    intro ℓ
    simp only [Finset.mem_union, T_flat, T_steep, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      by_cases hf : is_flat ℓ
      · exact Or.inl ⟨h, hf⟩
      · have hs : is_steep ℓ := (h_not_flat_iff_steep ℓ).mp hf
        exact Or.inr ⟨h, hs⟩
  have h_card : T_flat.card + T_steep.card = T.card := by
    rw [← Finset.card_union_of_disjoint h_disj, h_union]
  have h_half : 2 * T_flat.card ≥ T.card ∨ 2 * T_steep.card ≥ T.card := by
    by_contra h
    push Not at h
    omega
  have h_flat_prop : ∀ ℓ ∈ T_flat, is_flat ℓ := by
    intro ℓ hℓ
    exact (Finset.mem_filter.mp hℓ).2
  have h_steep_prop : ∀ ℓ ∈ T_steep, is_steep ℓ := by
    intro ℓ hℓ
    exact (Finset.mem_filter.mp hℓ).2
  exact ⟨T_flat, T_steep, h_union, h_disj, h_flat_prop, h_steep_prop, h_half⟩

/-- A large (≥ half) δ-separated subset of a (δ,s,C)-set is itself a
    (δ, s, C * 2 * Kpack)-set, where Kpack = affineLine_packing_constant. -/
lemma large_separated_subset_sset
    {δ s C : ℝ} {T T' : Finset AffineLine}
    (hδ_pos : 0 < δ) (hs_nonneg : 0 ≤ s) (hC_pos : 0 < C)
    (hT_sset : IsDeltaSSet δ s C (T : Set AffineLine))
    (hT'_sub : T' ⊆ T)
    (hT'_sep : Set.Pairwise (T' : Set AffineLine) (fun x y => δ ≤ dist x y))
    (hT'_nonempty : T'.Nonempty)
    (h_card : 2 * T'.card ≥ T.card) :
    IsDeltaSSet δ s (C * 2 * (MainAppendix.affineLine_packing_constant : ℝ)) (T' : Set AffineLine) := by
  let δnn : NNReal := δ.toNNReal
  have hδnn_eq : (δnn : ℝ) = δ := by simp [δnn, hδ_pos.le]
  let Kpack : ℕ := MainAppendix.affineLine_packing_constant
  have hK_pos : 0 < (Kpack : ℝ) := Nat.cast_pos.mpr MainAppendix.affineLine_packing_constant_pos
  let Ncover := fun (S : Set AffineLine) => (Metric.externalCoveringNumber δnn S : ENNReal)
  -- Ncover(T) ≤ |T|
  have h_self_cover : Metric.IsCover δnn (T : Set AffineLine) (T : Set AffineLine) := by
    intro x hx; exact ⟨x, hx, by simp [hδ_pos.le]⟩
  have h1 : Ncover (T : Set AffineLine) ≤ (↑T.card : ENNReal) := by
    have h : Metric.externalCoveringNumber δnn (T : Set AffineLine) ≤ (T : Set AffineLine).encard :=
      h_self_cover.externalCoveringNumber_le_encard
    have h_encard : (T : Set AffineLine).encard = ↑T.card := by simp
    rw [h_encard] at h
    have h' : (Metric.externalCoveringNumber δnn (T : Set AffineLine) : ENNReal) ≤ (↑T.card : ENNReal) := by
      exact_mod_cast h
    simpa [Ncover] using h'
  -- |T'| ≤ Kpack * Ncover(T')
  have hcov_fin : Ncover (T' : Set AffineLine) < ⊤ := by
    have hcover_self : Metric.IsCover δnn (T' : Set AffineLine) (T' : Set AffineLine) := by
      intro x hx; exact ⟨x, hx, by simp [hδ_pos.le]⟩
    have h : (Metric.externalCoveringNumber δnn (T' : Set AffineLine) : ENNReal) ≤
        ENat.toENNReal (T' : Set AffineLine).encard := by
      exact_mod_cast hcover_self.externalCoveringNumber_le_encard
    have h' : ENat.toENNReal (T' : Set AffineLine).encard < ⊤ := by
      simpa using T'.finite_toSet.encard_lt_top
    exact lt_of_le_of_lt h h'
  have h_pack_arg : ∀ (z : AffineLine) (S : Set AffineLine),
      Set.Pairwise S (fun x y => (δnn : ℝ) ≤ dist x y) →
      S ⊆ Metric.closedBall z (2 * (δnn : ℝ)) →
      S.Finite ∧ S.encard ≤ (Kpack : ENat) := by
    intro z S hS_sep hS_sub
    have hS_sep' : Set.Pairwise S (fun x y => δ ≤ dist x y) := by simpa [hδnn_eq] using hS_sep
    have hS_sub' : S ⊆ Metric.closedBall z (2 * δ) := by simpa [hδnn_eq] using hS_sub
    exact MainAppendix.affineLine_packing_bound δ hδ_pos hS_sep' z hS_sub'
  have h2 : ENat.toENNReal (T' : Set AffineLine).encard ≤
      (Kpack : ENNReal) * Ncover (T' : Set AffineLine) :=
    MainAppendix.separated_set_card_le_covering (hS_sep := by simpa [hδnn_eq] using hT'_sep)
      Kpack h_pack_arg hcov_fin
  have hT'_encard : (T' : Set AffineLine).encard = ↑T'.card := by simp
  rw [hT'_encard] at h2
  -- |T| ≤ 2 * |T'|
  have h3 : (↑T.card : ENNReal) ≤ 2 * (↑T'.card : ENNReal) := by exact_mod_cast h_card
  -- Ncover(T) ≤ 2 * Kpack * Ncover(T')
  have h4 : Ncover (T : Set AffineLine) ≤
      (2 * (Kpack : ENNReal)) * Ncover (T' : Set AffineLine) := by
    calc Ncover (T : Set AffineLine)
      ≤ (↑T.card : ENNReal) := h1
    _ ≤ 2 * (↑T'.card : ENNReal) := h3
    _ ≤ 2 * ((Kpack : ENNReal) * Ncover (T' : Set AffineLine)) := by gcongr <;> exact h2
    _ = (2 * (Kpack : ENNReal)) * Ncover (T' : Set AffineLine) := by ring
  -- S-set property for T'
  rcases hT_sset with ⟨hT_nonempty, hδ_pos', hC_pos', hs_nonneg', hmain⟩
  have hC'_pos : 0 < C * 2 * (Kpack : ℝ) := by positivity
  refine ⟨hT'_nonempty, hδ_pos', hC'_pos, hs_nonneg', ?_⟩
  intro x r hr
  have h_sub_int : (T' : Set AffineLine) ∩ Metric.closedBall x r ⊆
      (T : Set AffineLine) ∩ Metric.closedBall x r := by
    intro y hy; exact ⟨hT'_sub hy.1, hy.2⟩
  have h5 : Ncover ((T' : Set AffineLine) ∩ Metric.closedBall x r) ≤
      Ncover ((T : Set AffineLine) ∩ Metric.closedBall x r) := by
    have h_mono := Metric.externalCoveringNumber_mono_set (ε := δnn) h_sub_int
    have h' : (Metric.externalCoveringNumber δnn ((T' : Set AffineLine) ∩ Metric.closedBall x r) : ENNReal) ≤
        (Metric.externalCoveringNumber δnn ((T : Set AffineLine) ∩ Metric.closedBall x r) : ENNReal) := by
      exact ENat.toENNReal_le.mpr h_mono
    simpa [Ncover] using h'
  have h6 : Ncover ((T : Set AffineLine) ∩ Metric.closedBall x r) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * Ncover (T : Set AffineLine) :=
    hmain x r hr
  calc Ncover ((T' : Set AffineLine) ∩ Metric.closedBall x r)
    ≤ Ncover ((T : Set AffineLine) ∩ Metric.closedBall x r) := h5
  _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * Ncover (T : Set AffineLine) := h6
  _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
      ((2 * (Kpack : ENNReal)) * Ncover (T' : Set AffineLine)) := by gcongr <;> exact h4
  _ = ENNReal.ofReal (C * 2 * (Kpack : ℝ)) * (ENNReal.ofReal r) ^ s *
      Ncover (T' : Set AffineLine) := by
    have hC_nonneg : 0 ≤ C := hC_pos.le
    have h_mul : ENNReal.ofReal C * (2 * (Kpack : ENNReal)) =
        ENNReal.ofReal (C * 2 * (Kpack : ℝ)) := by
      have h1 : (2 * (Kpack : ENNReal)) = ENNReal.ofReal (2 * (Kpack : ℝ)) := by
        simp <;> norm_cast
      rw [h1]
      have h2 : ENNReal.ofReal C * ENNReal.ofReal (2 * (Kpack : ℝ)) =
          ENNReal.ofReal (C * (2 * (Kpack : ℝ))) := by
        have h_mul2 : ENNReal.ofReal (C * (2 * (Kpack : ℝ))) =
            ENNReal.ofReal C * ENNReal.ofReal (2 * (Kpack : ℝ)) := by
          exact ENNReal.ofReal_mul hC_nonneg
        exact h_mul2.symm
      have h3 : C * (2 * (Kpack : ℝ)) = C * 2 * (Kpack : ℝ) := by ring
      rw [h2, h3]
    have h_goal : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
        ((2 * (Kpack : ENNReal)) * Ncover (T' : Set AffineLine)) =
        ENNReal.ofReal (C * 2 * (Kpack : ℝ)) * (ENNReal.ofReal r) ^ s *
          Ncover (T' : Set AffineLine) := by
      have h3 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          ((2 * (Kpack : ENNReal)) * Ncover (T' : Set AffineLine)) =
          (ENNReal.ofReal C * (2 * (Kpack : ENNReal))) * (ENNReal.ofReal r) ^ s *
            Ncover (T' : Set AffineLine) := by ring
      rw [h3, h_mul] <;> ring
    exact h_goal

/-- Given a δ-separated tube family with S-set and near properties, produce a
    "good" subfamily satisfying slope bounds (v1≠0 and |slope|≤1), by partitioning
    into flat/steep and optionally swapping coordinates for the steep half.

    The good subfamily has ≥ |T|/2 elements and inherits the S-set property with
    constant C * 2 * affineLine_packing_constant. -/
lemma good_tube_family
    {δ s C : ℝ} {T : Finset AffineLine} {p : EuclideanPlane}
    [DecidableEq AffineLine]
    (hδ_pos : 0 < δ) (hs_nonneg : 0 ≤ s) (hC_pos : 0 < C)
    (hT_sset : IsDeltaSSet δ s C (T : Set AffineLine))
    (hT_sep : Set.Pairwise (T : Set AffineLine) (fun x y => δ ≤ dist x y))
    (hT_nonempty : T.Nonempty)
    (h_near : ∀ ℓ ∈ T, p ∈ Metric.cthickening δ ℓ.1)
    (hp : p ∈ Metric.closedBall 0 1) :
    ∃ (T_good : Finset AffineLine) (p_good : EuclideanPlane),
      (∀ ℓ ∈ T_good, (getDirV ℓ) 1 ≠ 0 ∧ |(affineLineParams ℓ).1| ≤ 1) ∧
      IsDeltaSSet δ s (C * 2 * (MainAppendix.affineLine_packing_constant : ℝ)) (T_good : Set AffineLine) ∧
      (∀ ℓ ∈ T_good, p_good ∈ Metric.cthickening δ ℓ.1) ∧
      p_good ∈ Metric.closedBall 0 1 ∧
      T_good.card ≥ T.card / 2 := by
  rcases partition_half (T := T) with ⟨T_flat, T_steep, h_union, h_disj, h_flat_prop, h_steep_prop, h_half⟩
  have h_flat_sub : T_flat ⊆ T := by
    have h : T_flat ⊆ T_flat ∪ T_steep := by simp
    rw [h_union] at h; exact h
  have h_steep_sub : T_steep ⊆ T := by
    have h : T_steep ⊆ T_flat ∪ T_steep := by simp
    rw [h_union] at h; exact h
  have h_flat_sep : Set.Pairwise (T_flat : Set AffineLine) (fun x y => δ ≤ dist x y) :=
    hT_sep.mono (show (T_flat : Set AffineLine) ⊆ (T : Set AffineLine) from by exact_mod_cast h_flat_sub)
  have h_steep_sep : Set.Pairwise (T_steep : Set AffineLine) (fun x y => δ ≤ dist x y) :=
    hT_sep.mono (show (T_steep : Set AffineLine) ⊆ (T : Set AffineLine) from by exact_mod_cast h_steep_sub)
  cases h_half with
  | inl h_flat_big =>
    have h_flat_nonempty : T_flat.Nonempty := by
      by_contra h
      have h' : T_flat.card = 0 := by simpa using h
      rw [h'] at h_flat_big
      have hT_card : T.card = 0 := by linarith
      have hT_empty : T = ∅ := Finset.card_eq_zero.mp hT_card
      simpa [hT_empty] using hT_nonempty
    have h_card : 2 * T_flat.card ≥ T.card := h_flat_big
    have h_sset_flat := large_separated_subset_sset hδ_pos hs_nonneg hC_pos hT_sset h_flat_sub h_flat_sep h_flat_nonempty h_card
    have h_near_flat : ∀ ℓ ∈ T_flat, p ∈ Metric.cthickening δ ℓ.1 := by
      intro ℓ hℓ; exact h_near ℓ (h_flat_sub hℓ)
    have h_flat_half : T_flat.card ≥ T.card / 2 := by omega
    exact ⟨T_flat, p, h_flat_prop, h_sset_flat, h_near_flat, hp, h_flat_half⟩
  | inr h_steep_big =>
    have h_steep_nonempty : T_steep.Nonempty := by
      by_contra h
      have h' : T_steep.card = 0 := by simpa using h
      rw [h'] at h_steep_big
      have hT_card : T.card = 0 := by linarith
      have hT_empty : T = ∅ := Finset.card_eq_zero.mp hT_card
      simpa [hT_empty] using hT_nonempty
    have h_card : 2 * T_steep.card ≥ T.card := h_steep_big
    have h_sset_steep := large_separated_subset_sset hδ_pos hs_nonneg hC_pos hT_sset h_steep_sub h_steep_sep h_steep_nonempty h_card
    let T_swap : Finset AffineLine := T_steep.image swapLine
    have h_swap_bounded : ∀ ℓ ∈ T_swap, (getDirV ℓ) 1 ≠ 0 ∧ |(affineLineParams ℓ).1| ≤ 1 := by
      intro ℓ hℓ
      rcases Finset.mem_image.mp hℓ with ⟨ℓ₀, hℓ₀, rfl⟩
      exact steep_swap_flat ℓ₀ (h_steep_prop ℓ₀ hℓ₀)
    have h_sset_swap : IsDeltaSSet δ s (C * 2 * (MainAppendix.affineLine_packing_constant : ℝ)) (T_swap : Set AffineLine) := by
      have h : (T_swap : Set AffineLine) = swapLine '' (T_steep : Set AffineLine) := by
        ext x; simp [T_swap] <;> rfl
      rw [h]
      exact swapLine_sset h_sset_steep
    have h_near_swap : ∀ ℓ ∈ T_swap, swapCoords p ∈ Metric.cthickening δ ℓ.1 := by
      intro ℓ hℓ
      rcases Finset.mem_image.mp hℓ with ⟨ℓ₀, hℓ₀, rfl⟩
      exact swapLine_near (h_near ℓ₀ (h_steep_sub hℓ₀))
    have hp_swap : swapCoords p ∈ Metric.closedBall 0 1 := by
      have h : dist (swapCoords p) 0 = dist p 0 := swapCoords_isometry.dist_eq p 0
      have h' : ‖swapCoords p‖ ≤ 1 := by
        have h'' : dist (swapCoords p) 0 = ‖swapCoords p‖ := by simp
        rw [h''] at h
        rw [h]
        simpa [Metric.mem_closedBall] using hp
      simpa [Metric.mem_closedBall] using h'
    have h_card_swap : T_swap.card = T_steep.card := by
      rw [Finset.card_image_of_injective _ swapLine_isometry.injective]
    have h_swap_half : T_swap.card ≥ T.card / 2 := by
      rw [h_card_swap]
      omega
    exact ⟨T_swap, swapCoords p, h_swap_bounded, h_sset_swap, h_near_swap, hp_swap, h_swap_half⟩

/-! ========================================================================
   Swap-line parameter conversion
   ======================================================================== -/

/-- Points (0,b) and (1,m+b) are on lineOfSlopeIntercept m b. -/
lemma point_on_lineOfSlopeIntercept (m b : ℝ) :
    TubesAndSlopes.mkPlane 0 b ∈ (lineOfSlopeIntercept m b).1 ∧
    TubesAndSlopes.mkPlane 1 (m + b) ∈ (lineOfSlopeIntercept m b).1 := by
  let p0 := TubesAndSlopes.mkPlane 0 b
  let p1 := TubesAndSlopes.mkPlane 1 (m + b)
  let v := DyadicCardToNcover.tubeDirV m
  have h0 : p0 ∈ (lineOfSlopeIntercept m b).1 := by
    simp [lineOfSlopeIntercept, AffineSubspace.mem_mk', p0]
  have h1 : p1 - p0 = v := by
    ext i
    fin_cases i <;> simp [p0, p1, v, DyadicCardToNcover.tubeDirV, TubesAndSlopes.mkPlane] <;> ring
  have h2 : p1 - p0 ∈ (lineOfSlopeIntercept m b).1.direction := by
    have h_dir : (lineOfSlopeIntercept m b).1.direction = Submodule.span ℝ {v} :=
      DyadicCardToNcover.lineOfSlopeIntercept_direction m b
    rw [h_dir, h1]
    exact Submodule.mem_span_singleton.mpr ⟨1, by simp⟩
  have h3 : p1 ∈ (lineOfSlopeIntercept m b).1 := by
    have h4 : p0 ∈ (lineOfSlopeIntercept m b).1 := h0
    have h5 : p1 - p0 ∈ (lineOfSlopeIntercept m b).1.direction := h2
    exact (AffineSubspace.vsub_right_mem_direction_iff_mem h0 p1).mp h2
  exact ⟨h0, h3⟩

/-- **Key conversion**: affineLineParams of a swapped lineOfSlopeIntercept
    equals the original (slope, intercept) pair.

    For a line y = m*x + b, swapping coordinates gives x = m*y + b.
    Thus `affineLineParams(swapLine ℓ) = (m, b)`.

    This is critical for the B1→A1 bridge: B1 produces lines with |m|≤1
    in y=mx+b convention; A1 expects |a|≤1 in x=ay+b convention.
    Swapping converts one to the other. -/
lemma swapLine_params_eq (m b : ℝ) :
    affineLineParams (swapLine (lineOfSlopeIntercept m b)) = (m, b) := by
  let ℓ := lineOfSlopeIntercept m b
  let ℓ' := swapLine ℓ
  let p0' := TubesAndSlopes.mkPlane b 0
  let p1' := TubesAndSlopes.mkPlane (m + b) 1

  have h_points_orig := point_on_lineOfSlopeIntercept m b
  have h_set : (ℓ'.1 : Set _) = swapCoords '' ℓ.1 := swapLine_set_eq ℓ

  have h0' : p0' ∈ ℓ'.1 := by
    have h_goal : p0' ∈ swapCoords '' ℓ.1 := by
      refine ⟨TubesAndSlopes.mkPlane 0 b, h_points_orig.1, ?_⟩
      ext i
      fin_cases i <;> simp [p0', swapCoords, TubesAndSlopes.mkPlane] <;> rfl
    have h_set' : (ℓ'.1 : Set _) = swapCoords '' ℓ.1 := h_set
    have h : p0' ∈ (ℓ'.1 : Set _) := by
      rw [h_set']
      exact h_goal
    exact h

  have h1' : p1' ∈ ℓ'.1 := by
    have h_goal : p1' ∈ swapCoords '' ℓ.1 := by
      refine ⟨TubesAndSlopes.mkPlane 1 (m + b), h_points_orig.2, ?_⟩
      ext i
      fin_cases i <;> simp [p1', swapCoords, TubesAndSlopes.mkPlane] <;> rfl
    have h_set' : (ℓ'.1 : Set _) = swapCoords '' ℓ.1 := h_set
    have h : p1' ∈ (ℓ'.1 : Set _) := by
      rw [h_set']
      exact h_goal
    exact h

  let v' := getDirV ℓ'
  have hv'_dir : v' ∈ ℓ'.1.direction := (getDirV_spec ℓ').1
  have hv'_ne : v' ≠ 0 := (getDirV_spec ℓ').2
  have h_span_v' : ℓ'.1.direction = ℝ ∙ v' := by
    have hfin : Module.finrank ℝ ℓ'.1.direction = 1 := ℓ'.2
    exact direction_eq_span hfin hv'_dir hv'_ne

  -- p1' - p0' is in the direction of ℓ'
  have h_diff_dir : p1' - p0' ∈ ℓ'.1.direction :=
    AffineSubspace.vsub_mem_direction h1' h0'

  -- v'1 ≠ 0 because p0' and p1' have different y-coordinates
  have h_v1_ne : v' 1 ≠ 0 := by
    rw [h_span_v'] at h_diff_dir
    rcases (Submodule.mem_span_singleton.mp h_diff_dir) with ⟨c, hc⟩
    have h_eq : (p1' - p0') 1 = c * (v' 1) := by
      have h : p1' - p0' = c • v' := hc.symm
      rw [h] <;> simp
    have h_val : (p1' - p0') 1 = 1 := by
      simp [p0', p1', TubesAndSlopes.mkPlane] <;> ring
    rw [h_val] at h_eq
    intro h_contra
    rw [h_contra] at h_eq
    norm_num at h_eq

  -- Apply affineLineParams_correct
  have h_correct := affineLineParams_correct ℓ' h_v1_ne
  let a' := (affineLineParams ℓ').1
  let b' := (affineLineParams ℓ').2

  have h_eq0 : p0' 0 = a' * p0' 1 + b' := h_correct p0' h0'
  have h_eq1 : p1' 0 = a' * p1' 1 + b' := h_correct p1' h1'

  have h_b' : b' = b := by
    have h_p0'0 : p0' 0 = b := by simp [p0', TubesAndSlopes.mkPlane]
    have h_p0'1 : p0' 1 = 0 := by simp [p0', TubesAndSlopes.mkPlane]
    rw [h_p0'0, h_p0'1] at h_eq0
    linarith
  have h_a' : a' = m := by
    have h_p1'0 : p1' 0 = m + b := by simp [p1', TubesAndSlopes.mkPlane]
    have h_p1'1 : p1' 1 = 1 := by simp [p1', TubesAndSlopes.mkPlane]
    rw [h_p1'0, h_p1'1] at h_eq1
    linarith [h_b']

  have h_main : (a', b') = (m, b) := by
    exact Prod.ext h_a' h_b'
  simpa [a', b'] using h_main

end CoordinatePartition
