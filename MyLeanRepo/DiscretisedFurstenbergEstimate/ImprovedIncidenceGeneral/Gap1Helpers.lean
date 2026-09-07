module

/-
  Affine normalization helpers for Gap 1 adapter.

  Defines S(p) = p/4 + (1/2, 1/2), mapping B(0,1) strictly into [0,1)².
  S is a homothety with scale 1/4, preserving line slopes.

  Provides:
  - S, S_line (AffineLine map)
  - Unit square containment
  - Distance scaling
  - Direction equality (honest slope preservation)
  - InStandardChart preservation
  - S-set, Ncover, incidence transfer
  - Offset bound via nearest-point property

  Whiteprint node: coarse_elimination_theorem / gap1_metric_to_dyadic
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.RescaleSsetEuclidean
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineDoubling
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable


noncomputable section

namespace DirecretisedFurstenbergEstimate.RegularIncidence

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
open DiscretisedFurstenbergEstimate.CoveringUtils
open DyadicCardToNcover

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Equality between the two line-of-slope-intercept constructors. -/
lemma lineOfSlopeIntercept_eq_mkSlopeIntercept (m b : ℝ) :
    lineOfSlopeIntercept m b = AffineLine.mkSlopeIntercept m b := by
  apply Subtype.ext
  have h_p : TubesAndSlopes.mkPlane 0 b = WithLp.toLp 2 ![0, b] := by
    ext i; fin_cases i <;> simp [TubesAndSlopes.mkPlane_apply0, TubesAndSlopes.mkPlane_apply1] <;> norm_num
  have h_v : tubeDirV m = WithLp.toLp 2 ![1, m] := by
    ext i; fin_cases i <;> simp [tubeDirV, TubesAndSlopes.mkPlane_apply0, TubesAndSlopes.mkPlane_apply1] <;> norm_num
  simp [lineOfSlopeIntercept, AffineLine.mkSlopeIntercept, h_p, h_v, AffineSubspace.direction_mk'] <;> rfl

/-- Convert chart hypothesis from mkSlopeIntercept to lineOfSlopeIntercept form. -/
lemma chart_mk_to_lineOf {E : Set AffineLine}
    (hE : ∀ ℓ ∈ E, ∃ (m b : ℝ), |m| ≤ 1 ∧ |b| ≤ 3 ∧ AffineLine.mkSlopeIntercept m b = ℓ) :
    ∀ ℓ ∈ E, ∃ (m b : ℝ), |m| ≤ 1 ∧ |b| ≤ 3 ∧ lineOfSlopeIntercept m b = ℓ := by
  intro ℓ hℓ
  rcases hE ℓ hℓ with ⟨m, b, hm, hb, h_eq⟩
  have h_eq' : lineOfSlopeIntercept m b = ℓ :=
    (lineOfSlopeIntercept_eq_mkSlopeIntercept m b).trans h_eq
  exact ⟨m, b, hm, hb, h_eq'⟩

/-- Wrapper for affine_line_factor2_doubling taking mkSlopeIntercept chart form. -/
lemma affine_doubling_mkSlope (δ : ℝ) (hδ_pos : 0 < δ) (E : Set AffineLine)
    (hE : ∀ ℓ ∈ E, ∃ (m b : ℝ), |m| ≤ 1 ∧ |b| ≤ 3 ∧ AffineLine.mkSlopeIntercept m b = ℓ) :
    Ncover δ E ≤ (262144 : ENNReal) * Ncover (2 * δ) E :=
  affine_line_factor2_doubling δ hδ_pos (chart_mk_to_lineOf hE)

/-- The constant vector (1/2, 1/2). -/
def halfVec : Plane := WithLp.toLp 2 ![1 / 2, 1 / 2]

/-- Linear map: scaling by 1/4. -/
def quarterScaling : Plane →ₗ[ℝ] Plane :=
  (1 / 4 : ℝ) • LinearMap.id

/-- Affine normalization map: S(p) = p/4 + (1/2, 1/2). -/
def S_affineMap : Plane →ᵃ[ℝ] Plane :=
  ⟨fun p => (1 / 4 : ℝ) • p + halfVec,
   quarterScaling,
   fun p v => by
     simp [quarterScaling, smul_add]
     <;> abel⟩

/-- S(p) = p/4 + (1/2, 1/2). -/
def S (p : Plane) : Plane := S_affineMap p

lemma S_apply (p : Plane) : S p = (1 / 4 : ℝ) • p + halfVec := by rfl

/-! ========================================================================
   1. Unit square containment
   ======================================================================== -/

/-- Coordinate absolute value bounded by norm. -/
lemma coord_abs_le_norm {p : Plane} {i : Fin 2} : |p i| ≤ ‖p‖ := by
  have h_sum2 : ‖p‖^2 = (p 0)^2 + (p 1)^2 := by
    have h6 : ‖p‖ = Real.sqrt ((p 0)^2 + (p 1)^2) := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> ring
    rw [h6]
    have h7 : 0 ≤ (p 0)^2 + (p 1)^2 := by positivity
    rw [Real.sq_sqrt h7] <;> ring
  have h_i2 : (p i)^2 ≤ ‖p‖^2 := by
    rw [h_sum2]
    fin_cases i
    · have h : (p 0)^2 ≤ (p 0)^2 + (p 1)^2 := by
        have h' : 0 ≤ (p 1)^2 := by positivity
        linarith
      exact h
    · have h : (p 1)^2 ≤ (p 0)^2 + (p 1)^2 := by
        have h' : 0 ≤ (p 0)^2 := by positivity
        linarith
      exact h
  have h4 : 0 ≤ |p i| := by positivity
  have h5 : 0 ≤ ‖p‖ := by positivity
  nlinarith [sq_abs (p i)]

/-- S maps B(0,1) strictly into [0,1)². -/
lemma S_image_unitSquare {P : Set Plane}
    (hP_sub : P ⊆ Metric.closedBall (0 : Plane) 1) :
    ∀ p ∈ S '' P, 0 ≤ p 0 ∧ p 0 < 1 ∧ 0 ≤ p 1 ∧ p 1 < 1 := by
  intro q hq
  rcases hq with ⟨p, hp, rfl⟩
  have hp_ball : p ∈ Metric.closedBall (0 : Plane) 1 := hP_sub hp
  have h_norm : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hp_ball
  have h0 : |p 0| ≤ 1 := by
    have h : |p 0| ≤ ‖p‖ := coord_abs_le_norm
    linarith
  have h1 : |p 1| ≤ 1 := by
    have h : |p 1| ≤ ‖p‖ := coord_abs_le_norm
    linarith
  have hS0 : (S p) 0 = p 0 / 4 + 1 / 2 := by
    simp [S_apply, halfVec] <;> ring
  have hS1 : (S p) 1 = p 1 / 4 + 1 / 2 := by
    simp [S_apply, halfVec] <;> ring
  rw [hS0, hS1]
  have h_abs0 : -1 ≤ p 0 ∧ p 0 ≤ 1 := abs_le.mp h0
  have h_abs1 : -1 ≤ p 1 ∧ p 1 ≤ 1 := abs_le.mp h1
  constructor
  · linarith
  · constructor
    · linarith
    · constructor
      · linarith
      · linarith

/-! ========================================================================
   2. Distance scaling
   ======================================================================== -/

/-- S scales distances by exactly 1/4. -/
lemma S_dist (p q : Plane) : dist (S p) (S q) = (1 / 4 : ℝ) * dist p q := by
  have h1 : S p = (1 / 4 : ℝ) • p + halfVec := S_apply p
  have h2 : S q = (1 / 4 : ℝ) • q + halfVec := S_apply q
  have h3 : S p - S q = (1 / 4 : ℝ) • (p - q) := by
    rw [h1, h2]
    rw [smul_sub]
    <;> abel
  rw [dist_eq_norm, dist_eq_norm, h3]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 1 / 4 by norm_num)]
  <;> ring

/-! ========================================================================
   3. AffineLine map
   ======================================================================== -/

/-- Map an AffineLine through S. -/
noncomputable def S_line (ℓ : AffineLine) : AffineLine :=
  let f := S_affineMap
  let img := AffineSubspace.map f ℓ.1
  have h_dir : img.direction = Submodule.map f.linear ℓ.1.direction :=
    AffineSubspace.map_direction f ℓ.1
  have h_inj : Function.Injective f.linear := by
    intro x y h
    have h' : quarterScaling x = quarterScaling y := h
    have h'' : x = y := by
      simpa [quarterScaling] using congr_arg (fun z : Plane => (4 : ℝ) • z) h'
    exact h''
  let g : ℓ.1.direction →ₗ[ℝ] Plane := f.linear.comp ℓ.1.direction.subtype
  have hg_inj : Function.Injective g := by
    intro a b h
    exact Subtype.ext (h_inj h)
  let e := LinearEquiv.ofInjective g hg_inj
  have h_range : LinearMap.range g = Submodule.map f.linear ℓ.1.direction := by
    ext z
    simp [g, LinearMap.mem_range, Submodule.mem_map] <;> aesop
  have h_finrank : Module.finrank ℝ (Submodule.map f.linear ℓ.1.direction) =
      Module.finrank ℝ ℓ.1.direction := by
    rw [← h_range]
    exact (LinearEquiv.finrank_eq e).symm
  have h_main : Module.finrank ℝ img.direction = 1 := by
    rw [h_dir, h_finrank, ℓ.2]
  ⟨img, h_main⟩

/-- The image line's underlying affine subspace. -/
lemma S_line_subspace (ℓ : AffineLine) :
    (S_line ℓ).1 = AffineSubspace.map S_affineMap ℓ.1 := by
  rfl

/-- The image line's underlying set is S '' ℓ.1. -/
lemma S_line_set (ℓ : AffineLine) :
    ((S_line ℓ).1 : Set Plane) = S '' ℓ.1 := by
  rw [S_line_subspace]
  <;> rfl

/-- p ∈ ℓ.1 iff S p ∈ (S_line ℓ).1. -/
lemma S_line_incidence (p : Plane) (ℓ : AffineLine) :
    p ∈ ℓ.1 ↔ S p ∈ (S_line ℓ).1 := by
  have h_set : ((S_line ℓ).1 : Set Plane) = S '' (ℓ.1 : Set Plane) := S_line_set ℓ
  have h_S_inj : Function.Injective S := by
    intro x y h
    have h' : (1 / 4 : ℝ) • x + halfVec = (1 / 4 : ℝ) • y + halfVec := h
    have h'' : (1 / 4 : ℝ) • x = (1 / 4 : ℝ) • y := by simpa using h'
    have h3 : x = y := by
      apply_fun (fun z : Plane => (4 : ℝ) • z) at h''
      simpa using h''
    exact h3
  constructor
  · intro h
    exact ⟨p, h, rfl⟩
  · intro h
    have h4 : S p ∈ S '' (ℓ.1 : Set Plane) := by
      have h5 : S p ∈ (S_line ℓ).1 := h
      have h6 : ((S_line ℓ).1 : Set Plane) = S '' (ℓ.1 : Set Plane) := h_set
      exact h6 ▸ h5
    rcases h4 with ⟨q, hq, h_eq⟩
    have h6 : q = p := h_S_inj h_eq
    rw [h6] at hq
    exact hq

/-! ========================================================================
   4. Direction equality and InStandardChart preservation
   ======================================================================== -/

/-- S_line preserves the direction subspace (homothety maps lines to parallel
    lines). Honest slope preservation — no bogus vertical fallback. -/
lemma S_line_direction (ℓ : AffineLine) :
    (S_line ℓ).1.direction = ℓ.1.direction := by
  have h1 : (S_line ℓ).1.direction =
      Submodule.map S_affineMap.linear ℓ.1.direction := by
    rw [S_line_subspace]
    exact AffineSubspace.map_direction S_affineMap ℓ.1
  rw [h1]
  have h2 : Submodule.map S_affineMap.linear ℓ.1.direction = ℓ.1.direction := by
    ext z
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ℓ.1.direction.smul_mem (1 / 4 : ℝ) hx
    · intro hz
      refine ⟨(4 : ℝ) • z, ℓ.1.direction.smul_mem (4 : ℝ) hz, ?_⟩
      have h4 : S_affineMap.linear ((4 : ℝ) • z) = z := by
        simp [S_affineMap, quarterScaling] <;> simp [smul_smul] <;> norm_num
      exact h4
  exact h2

/-- Membership characterization for mkSlopeIntercept. -/
lemma mkSlopeIntercept_mem_iff {m b : ℝ} {p : Plane} :
    p ∈ (AffineLine.mkSlopeIntercept m b).1 ↔ p 1 = m * p 0 + b := by
  let v : Plane := WithLp.toLp 2 ![1, m]
  let pt : Plane := WithLp.toLp 2 ![0, b]
  let dir : Submodule ℝ Plane := Submodule.span ℝ {v}
  have h_unfold : (AffineLine.mkSlopeIntercept m b).1 = AffineSubspace.mk' pt dir := by
    rfl
  rw [h_unfold]
  have h_main : p ∈ AffineSubspace.mk' pt dir ↔ p - pt ∈ dir :=
    AffineSubspace.mem_mk'
  rw [h_main]
  have h_dir : p - pt ∈ dir ↔ ∃ (c : ℝ), p - pt = c • v := by
    have h1 : p - pt ∈ Submodule.span ℝ {v} ↔ ∃ (c : ℝ), p - pt = c • v := by
      rw [Submodule.mem_span_singleton]
      constructor
      · rintro ⟨c, hc⟩; exact ⟨c, hc.symm⟩
      · rintro ⟨c, hc⟩; exact ⟨c, hc.symm⟩
    exact h1
  rw [h_dir]
  constructor
  · rintro ⟨c, hc⟩
    have h_eq : ∀ (i : Fin 2), (p - pt) i = (c • v) i := by
      intro i
      exact congr_arg (fun x : Plane => x i) hc
    have h0 : (p - pt) 0 = c := by
      have h := h_eq 0
      simpa [v] using h
    have h1 : (p - pt) 1 = c * m := by
      have h := h_eq 1
      simpa [v] using h
    have h_p0 : p 0 - pt 0 = c := by simpa [pt] using h0
    have h_p1 : p 1 - pt 1 = c * m := by simpa [pt] using h1
    have h_pt0 : pt 0 = 0 := by simp [pt]
    have h_pt1 : pt 1 = b := by simp [pt]
    have h2 : p 0 = c := by linarith
    have h3 : p 1 = c * m + b := by linarith
    have h4 : p 1 = m * p 0 + b := by
      calc p 1 = c * m + b := h3
        _ = m * c + b := by ring
        _ = m * p 0 + b := by rw [h2]
    exact h4
  · intro h
    refine ⟨p 0, ?_⟩
    ext i
    fin_cases i <;> simp [v, pt, h] <;> ring

/-- Offset formula for mkSlopeIntercept: `offset = b • offsetVec m`. -/
lemma mkSlopeIntercept_offset_formula (m b : ℝ) :
    (AffineLine.mkSlopeIntercept m b).offset = b • offsetVec m := by
  let v : Plane := WithLp.toLp 2 ![1, m]
  let pt : Plane := WithLp.toLp 2 ![0, b]
  let dir : Submodule ℝ Plane := Submodule.span ℝ {v}
  let aff : AffineSubspace ℝ Plane := AffineSubspace.mk' pt dir
  let P := dir.starProjection
  have h_unfold : (AffineLine.mkSlopeIntercept m b).1 = aff := by rfl
  have h_dir : aff.direction = dir := by
    simp [aff, AffineSubspace.direction_mk'] <;> rfl
  have h_p_mem : pt ∈ aff := by exact AffineSubspace.self_mem_mk' pt dir
  have h_main : (EuclideanGeometry.orthogonalProjection aff 0 : Plane) = P (0 - pt) + pt := by
    have h := EuclideanGeometry.orthogonalProjection_apply_mem aff (x := pt) h_p_mem (p := 0)
    have h_eq : ∀ (x : Plane), aff.direction.orthogonalProjectionOnto x = P x := by
      intro x; rw [h_dir] <;> rfl
    have h' : (EuclideanGeometry.orthogonalProjection aff 0 : Plane) =
        aff.direction.orthogonalProjectionOnto (0 - pt) + pt := by simpa using h
    rw [h', h_eq (0 - pt)]
  have hPp : P pt = ((b * m) / (1 + m^2)) • v := by
    have h : P pt = (inner ℝ v pt / ‖v‖ ^ 2) • v :=
      Submodule.starProjection_singleton (𝕜 := ℝ) (v := v) (w := pt)
    rw [h]
    have h_inner : inner ℝ v pt = b * m := by
      rw [PiLp.inner_apply, Fin.sum_univ_two] <;> simp [v, pt] <;> ring
    have h_norm : ‖v‖ ^ 2 = 1 + m^2 := by
      simp [v, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> ring
    rw [h_inner, h_norm] <;> ring
  have h0 : P (0 - pt) = -P pt := by
    have h : P (0 - pt) = P (-pt) := by simp
    rw [h, ContinuousLinearMap.map_neg P pt]
  have h_goal : (P (0 - pt) + pt : Plane) = b • offsetVec m := by
    rw [h0, hPp]
    ext i
    fin_cases i
    · simp [v, pt, offsetVec, TubesAndSlopes.mkPlane, smul_eq_mul] <;> field_simp <;> ring
    · simp [v, pt, offsetVec, TubesAndSlopes.mkPlane, smul_eq_mul] <;> field_simp <;> ring
  have h_final : (AffineLine.mkSlopeIntercept m b).offset = (EuclideanGeometry.orthogonalProjection aff 0 : Plane) := by
    simp [AffineLine.offset, h_unfold]
  rw [h_final, h_main, h_goal]

/-- If ℓ is in the standard chart, S_line ℓ is also in the standard chart,
    with the same slope. -/
lemma S_line_inChart {ℓ : AffineLine} (h : InStandardChart.inChart ℓ) :
    InStandardChart.inChart (S_line ℓ) := by
  rcases h with ⟨m, b, hm_bound, rfl⟩
  let q : Plane := S (AffineLine.mkSlopeIntercept m b).offset
  have hq_in : q ∈ (S_line (AffineLine.mkSlopeIntercept m b)).1 :=
    (S_line_incidence (AffineLine.mkSlopeIntercept m b).offset
      (AffineLine.mkSlopeIntercept m b)).mp
      (AffineLine.offset_mem (AffineLine.mkSlopeIntercept m b))
  let b' : ℝ := q 1 - m * q 0
  have h_dir_eq : (S_line (AffineLine.mkSlopeIntercept m b)).1.direction =
      (AffineLine.mkSlopeIntercept m b').1.direction := by
    have h1 : (S_line (AffineLine.mkSlopeIntercept m b)).1.direction =
        (AffineLine.mkSlopeIntercept m b).1.direction :=
      S_line_direction (AffineLine.mkSlopeIntercept m b)
    rw [h1]
    have h2 : (AffineLine.mkSlopeIntercept m b).1.direction =
        (AffineLine.mkSlopeIntercept m b').1.direction := by
      simp [AffineLine.mkSlopeIntercept]
      <;> rfl
    exact h2
  have h_common : q ∈ (S_line (AffineLine.mkSlopeIntercept m b)).1 ∧
      q ∈ (AffineLine.mkSlopeIntercept m b').1 := by
    constructor
    · exact hq_in
    · rw [mkSlopeIntercept_mem_iff]
      simp [b'] <;> ring
  have h_eq : (S_line (AffineLine.mkSlopeIntercept m b)).1 =
      (AffineLine.mkSlopeIntercept m b').1 :=
    AffineSubspace.ext_of_direction_eq h_dir_eq ⟨q, h_common.1, h_common.2⟩
  have h_line_eq : S_line (AffineLine.mkSlopeIntercept m b) =
      AffineLine.mkSlopeIntercept m b' := by
    apply Subtype.ext
    exact h_eq
  rw [h_line_eq]
  exact ⟨m, b', hm_bound, rfl⟩

/-! ========================================================================
   5. S-set transfer
   ======================================================================== -/

/-- S-set transfer under S: if P is (δ,t,C)-set, S '' P is (δ/4, t, C*4^t)-set. -/
lemma S_sset {δ t C : ℝ} {P : Set Plane}
    (hP : IsDeltaSSet δ t C P) :
    IsDeltaSSet (δ / 4) t (C * (4 : ℝ)^t) (S '' P) := by
  have h1_raw : IsDeltaSSet ((1 / 4 : ℝ) * δ) t (C * (1 / 4 : ℝ)^(-t))
      ((fun x : Plane => (1 / 4 : ℝ) • x) '' P) :=
    rescale_sset_euclidean (c := (1 / 4 : ℝ)) (by norm_num) hP
  have hδ_eq : (1 / 4 : ℝ) * δ = δ / 4 := by ring
  have hC_eq : C * (1 / 4 : ℝ)^(-t) = C * (4 : ℝ)^t := by
    have hpos' : (0 : ℝ) ≤ 1 / 4 := by norm_num
    have h1 : (1 / 4 : ℝ)^(-t) = ((1 / 4 : ℝ)^t)⁻¹ :=
      Real.rpow_neg hpos' t
    have h_pos : 0 < (1 / 4 : ℝ)^t := by positivity
    have h_mul : (1 / 4 : ℝ)^t * (4 : ℝ)^t = 1 := by
      have h_eq : ((1 / 4 : ℝ) * (4 : ℝ))^t = (1 / 4 : ℝ)^t * (4 : ℝ)^t := Real.mul_rpow (by norm_num) (by norm_num)
      have h2 : (1 / 4 : ℝ) * (4 : ℝ) = 1 := by norm_num
      have h3 : (1 : ℝ)^t = 1 := by simp
      rw [h2] at h_eq
      rw [h3] at h_eq
      exact h_eq.symm
    have h_inv : ((1 / 4 : ℝ)^t)⁻¹ = (4 : ℝ)^t := inv_eq_of_mul_eq_one_right h_mul
    have h : (1 / 4 : ℝ)^(-t) = (4 : ℝ)^t := by
      rw [h1, h_inv]
    rw [h]
  have h1 : IsDeltaSSet (δ / 4) t (C * (4 : ℝ)^t)
      ((fun x : Plane => (1 / 4 : ℝ) • x) '' P) := by
    rw [hδ_eq, hC_eq] at h1_raw
    exact h1_raw
  have h2 : IsDeltaSSet (δ / 4) t (C * (4 : ℝ)^t)
      ((fun x : Plane => x + halfVec) '' (((fun x : Plane => (1 / 4 : ℝ) • x) '' P))) :=
    translate_sset_euclidean h1
  have h3 : (fun x : Plane => x + halfVec) '' ((fun x : Plane => (1 / 4 : ℝ) • x) '' P) = S '' P := by
    ext z
    simp only [S_apply, Set.mem_image]
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, by simp [halfVec] <;> abel⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(1 / 4 : ℝ) • x, ⟨x, hx, rfl⟩, by simp [halfVec] <;> abel⟩
  rw [h3] at h2
  exact h2

/-! ========================================================================
   6. Ncover transfer
   ======================================================================== -/

/-- Translation by `v` as an `IsometryEquiv`. -/
def translationEquiv (v : Plane) : Plane ≃ᵢ Plane :=
  { toFun := fun x => x + v
    invFun := fun y => y - v
    left_inv := by intro x; simp [add_sub_cancel]
    right_inv := by intro y; simp [sub_add_cancel]
    isometry_toFun := by
      intro x y
      rw [edist_dist, edist_dist]
      have h : dist (x + v) (y + v) = dist x y := by
        simp [dist_eq_norm] <;> abel
      rw [h] }

/-- Covering number is invariant under translation. -/
lemma ncover_translate {ε : NNReal} {P : Set Plane} {v : Plane} :
    Metric.externalCoveringNumber ε ((fun x : Plane => x + v) '' P) =
    Metric.externalCoveringNumber ε P :=
  externalCoveringNumber_image_isometryEquiv (translationEquiv v)

/-- Covering number scales correctly: Ncover(c·δ, c•P) = Ncover(δ, P) for 0 < c ≤ 1.

    Uses `externalCoveringNumber_image_lipschitz` in both directions:
    scaling by c is c-Lipschitz, and its inverse (scaling by 1/c) is (1/c)-Lipschitz. -/
lemma ncover_scale {c δ : ℝ} (hc_pos : 0 < c) (hc_le_one : c ≤ 1)
    (hδ_pos : 0 < δ) {P : Set Plane} :
    Ncover (c * δ) ((fun x : Plane => c • x) '' P) = Ncover δ P := by
  let scale : Plane → Plane := fun x => c • x
  let unscale : Plane → Plane := fun x => (1 / c) • x
  let Kc : NNReal := ⟨c, hc_pos.le⟩
  let Kinv : NNReal := ⟨1 / c, (div_pos zero_lt_one hc_pos).le⟩

  have h_scale_lip : LipschitzWith Kc scale := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h : dist (scale x) (scale y) = c * dist x y := by
      have h1 : scale x - scale y = c • (x - y) := by
        simp [scale, smul_sub] <;> abel
      rw [dist_eq_norm, dist_eq_norm, h1, norm_smul]
      <;> rw [Real.norm_eq_abs, abs_of_pos hc_pos] <;> ring
    rw [h] <;> exact le_refl _

  have h_unscale_lip : LipschitzWith Kinv unscale := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hpos' : 0 < 1 / c := div_pos zero_lt_one hc_pos
    have h : dist (unscale x) (unscale y) = (1 / c) * dist x y := by
      have h1 : unscale x - unscale y = (1 / c) • (x - y) := by
        simp [unscale, smul_sub] <;> abel
      rw [dist_eq_norm, dist_eq_norm, h1, norm_smul]
      <;> rw [Real.norm_eq_abs, abs_of_pos hpos'] <;> ring
    rw [h] <;> exact le_refl _

  have h_left_inv : ∀ x, unscale (scale x) = x := by
    intro x
    have h : (1 / c) • (c • x) = x := by
      have h1 : (1 / c) • (c • x) = ((1 / c) * c) • x := by exact smul_smul (1 / c) c x
      rw [h1]
      have h2 : (1 / c) * c = 1 := by field_simp [hc_pos.ne']
      rw [h2, one_smul]
    exact h
  have h_image_inv : unscale '' (scale '' P) = P := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨x, hx, rfl⟩
      rw [h_left_inv x] <;> exact hx
    · intro hz
      refine ⟨scale z, ?_, ?_⟩
      · exact ⟨z, hz, rfl⟩
      · exact h_left_inv z

  let ε2 : NNReal := δ.toNNReal
  have hε2_pos : 0 < ε2 := by
    simp [ε2, hδ_pos] <;> exact_mod_cast hδ_pos
  have hKc_coe : (Kc : ℝ) = c := by
    dsimp only [Kc] <;> rfl
  have hε2_coe : (ε2 : ℝ) = δ := by
    dsimp only [ε2] <;> simp [hδ_pos.le]
  have hKcε2 : ((Kc * ε2 : NNReal) : ℝ) = c * δ := by
    rw [NNReal.coe_mul, hKc_coe, hε2_coe] <;> ring
  have hε1_eq : Kc * ε2 = (c * δ).toNNReal := by
    apply NNReal.coe_injective
    have hpos : 0 ≤ c * δ := by positivity
    have h : (((c * δ).toNNReal : NNReal) : ℝ) = c * δ := Real.coe_toNNReal (c * δ) hpos
    rw [hKcε2, h]
  have hKinv_coe : (Kinv : ℝ) = 1 / c := by
    dsimp only [Kinv] <;> rfl
  have hKinvKc : Kinv * Kc = 1 := by
    apply NNReal.coe_injective
    have h : ((Kinv * Kc : NNReal) : ℝ) = (1 : ℝ) := by
      rw [NNReal.coe_mul, hKinv_coe, hKc_coe]
      <;> field_simp [hc_pos.ne'] <;> ring
    rw [h]
    <;> simp

  have h_forward : Metric.externalCoveringNumber (Kc * ε2) (scale '' P) ≤
      Metric.externalCoveringNumber ε2 P :=
    externalCoveringNumber_image_lipschitz (hf := h_scale_lip)

  have h_backward_raw : Metric.externalCoveringNumber (Kinv * (Kc * ε2)) (unscale '' (scale '' P)) ≤
      Metric.externalCoveringNumber (Kc * ε2) (scale '' P) :=
    externalCoveringNumber_image_lipschitz (hf := h_unscale_lip)

  have h_mul : Kinv * (Kc * ε2) = ε2 := by
    calc Kinv * (Kc * ε2)
      = (Kinv * Kc) * ε2 := by rw [mul_assoc]
    _ = (1 : NNReal) * ε2 := by rw [hKinvKc]
    _ = ε2 := by simp

  rw [h_mul, h_image_inv] at h_backward_raw
  have h_backward : Metric.externalCoveringNumber ε2 P ≤
      Metric.externalCoveringNumber (Kc * ε2) (scale '' P) := h_backward_raw
  rw [hε1_eq] at h_forward
  rw [hε1_eq] at h_backward
  have h_final : Metric.externalCoveringNumber (c * δ).toNNReal (scale '' P) =
      Metric.externalCoveringNumber ε2 P := le_antisymm h_forward h_backward
  simpa [Ncover, ε2] using h_final

/-- Ncover(δ/4, S '' P) = Ncover(δ, P).

    Proved via Lipschitz bounds for scaling and translation invariance,
    using `externalCoveringNumber_image_lipschitz` and
    `externalCoveringNumber_image_isometryEquiv` from CoveringUtils. -/
lemma S_ncover {δ : ℝ} (hδ_pos : 0 < δ) {P : Set Plane} :
    Ncover (δ / 4) (S '' P) = Ncover δ P := by
  let scale : Plane → Plane := fun x => (1 / 4 : ℝ) • x
  let τ : Plane → Plane := fun x => x + halfVec
  have h1 : S = τ ∘ scale := by funext x; rfl
  have h_comp : S '' P = τ '' (scale '' P) := by
    rw [h1, Set.image_comp]
  have hδ4 : δ / 4 = (1 / 4 : ℝ) * δ := by ring
  have h_scale_eq : Ncover (δ / 4) (scale '' P) = Ncover δ P := by
    rw [hδ4]
    exact ncover_scale (show (0 : ℝ) < 1 / 4 by norm_num) (by norm_num) hδ_pos
  have h_scale_eq' : Metric.externalCoveringNumber (δ / 4).toNNReal (scale '' P) =
      Metric.externalCoveringNumber δ.toNNReal P := by
    simpa [Ncover] using h_scale_eq
  have h_translate : Metric.externalCoveringNumber (δ / 4).toNNReal (τ '' (scale '' P)) =
      Metric.externalCoveringNumber (δ / 4).toNNReal (scale '' P) :=
    ncover_translate (ε := (δ / 4).toNNReal) (P := scale '' P) (v := halfVec)
  have h_main : Metric.externalCoveringNumber (δ / 4).toNNReal (S '' P) =
      Metric.externalCoveringNumber δ.toNNReal P := by
    calc Metric.externalCoveringNumber (δ / 4).toNNReal (S '' P)
      = Metric.externalCoveringNumber (δ / 4).toNNReal (τ '' (scale '' P)) := by rw [h_comp]
    _ = Metric.externalCoveringNumber (δ / 4).toNNReal (scale '' P) := h_translate
    _ = Metric.externalCoveringNumber δ.toNNReal P := h_scale_eq'
  simpa [Ncover] using h_main

/-! ========================================================================
   7. Incidence transfer
   ======================================================================== -/

/-- Incidence transfer: p ∈ cthickening δ ℓ.1 iff
    S p ∈ cthickening (δ/4) (S_line ℓ).1.

    Uses the nearest-point property of affine subspaces to establish the
    two-sided infEDist scaling bound. -/
lemma S_incidence {δ : ℝ} (hδ : 0 ≤ δ) {p : Plane} {ℓ : AffineLine} :
    p ∈ Metric.cthickening δ ℓ.1 ↔
    S p ∈ Metric.cthickening (δ / 4) (S_line ℓ).1 := by
  let f := S
  let s_set : Set Plane := ℓ.1
  let s'_set : Set Plane := (S_line ℓ).1
  have h_set_eq : (s'_set : Set Plane) = f '' s_set := S_line_set ℓ
  let c : ENNReal := ENNReal.ofReal (1 / 4 : ℝ)
  have hc_pos : c ≠ 0 := by simp [c] <;> norm_num
  have hc_top : c ≠ ⊤ := by simp [c] <;> norm_num

  have h_edist_scale : ∀ (x y : Plane), edist (f x) (f y) = c * edist x y := by
    intro x y
    have h1 : edist (f x) (f y) = ENNReal.ofReal (dist (f x) (f y)) := by rw [edist_dist]
    rw [h1, edist_dist]
    have h2 : dist (f x) (f y) = (1 / 4 : ℝ) * dist x y := S_dist x y
    rw [h2]
    have h3 : ENNReal.ofReal ((1 / 4 : ℝ) * dist x y) = c * ENNReal.ofReal (dist x y) := by
      have h_pos : (0 : ℝ) ≤ 1 / 4 := by norm_num
      rw [ENNReal.ofReal_mul h_pos]
      <;> rfl
    rw [h3]

  -- Nearest point in s_set to p (orthogonal projection)
  let y0_sub := EuclideanGeometry.orthogonalProjection ℓ.1 p
  let y0 : Plane := (y0_sub : Plane)
  have hy0_mem : y0 ∈ s_set := y0_sub.prop
  have h_nearest : dist p y0 = Metric.infDist p s_set :=
    EuclideanGeometry.dist_orthogonalProjection_eq_infDist ℓ.1 p

  have h_infEDist_eq : Metric.infEDist p s_set = edist p y0 := by
    have h1 : ∀ y ∈ s_set, edist p y0 ≤ edist p y := by
      intro y hy
      have h2 : dist p y0 ≤ dist p y := by
        rw [h_nearest]
        exact Metric.infDist_le_dist_of_mem hy
      have h2' : edist p y0 ≤ edist p y := by
        rw [edist_dist, edist_dist]
        exact ENNReal.ofReal_le_ofReal h2
      exact h2'
    have h3 : Metric.infEDist p s_set ≤ edist p y0 :=
      Metric.infEDist_le_edist_of_mem hy0_mem
    have h4 : edist p y0 ≤ Metric.infEDist p s_set :=
      Metric.le_infEDist.mpr h1
    exact le_antisymm h3 h4

  -- Upper bound: infEDist (f p) s'_set ≤ c * infEDist p s_set
  have h_upper : Metric.infEDist (f p) s'_set ≤ c * Metric.infEDist p s_set := by
    rw [h_infEDist_eq]
    have h5 : f y0 ∈ s'_set := by
      rw [h_set_eq]
      exact ⟨y0, hy0_mem, rfl⟩
    have h6 : Metric.infEDist (f p) s'_set ≤ edist (f p) (f y0) :=
      Metric.infEDist_le_edist_of_mem h5
    rw [h_edist_scale p y0] at h6
    exact h6

  -- Lower bound: c * infEDist p s_set ≤ infEDist (f p) s'_set
  have h_lower : c * Metric.infEDist p s_set ≤ Metric.infEDist (f p) s'_set := by
    rw [h_set_eq]
    apply Metric.le_infEDist.mpr
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    have h7 : Metric.infEDist p s_set ≤ edist p y :=
      Metric.infEDist_le_edist_of_mem hy
    have h8 : c * Metric.infEDist p s_set ≤ c * edist p y :=
      mul_le_mul_left' h7 c
    rw [h_edist_scale p y]
    exact h8

  have h_inf_scale : Metric.infEDist (f p) s'_set = c * Metric.infEDist p s_set :=
    le_antisymm h_upper h_lower

  have h5 : ENNReal.ofReal (δ / 4) = c * ENNReal.ofReal δ := by
    have h : ENNReal.ofReal (δ * (1 / 4 : ℝ)) = ENNReal.ofReal δ * c := by
      rw [ENNReal.ofReal_mul hδ]
      <;> rfl
    have h2 : δ / 4 = δ * (1 / 4 : ℝ) := by ring
    rw [h2, h]
    <;> ring

  have h_cancel : ∀ {a b : ENNReal}, c * a ≤ c * b → a ≤ b := by
    intro a b h
    have hcinv : c⁻¹ * c = 1 := by
      rw [mul_comm]
      exact ENNReal.mul_inv_cancel hc_pos hc_top
    have h' : c⁻¹ * (c * a) ≤ c⁻¹ * (c * b) := mul_le_mul_left' h c⁻¹
    have h1 : c⁻¹ * (c * a) = a := by
      calc c⁻¹ * (c * a)
        = (c⁻¹ * c) * a := by rw [mul_assoc]
      _ = 1 * a := by rw [hcinv]
      _ = a := by simp
    have h2 : c⁻¹ * (c * b) = b := by
      calc c⁻¹ * (c * b)
        = (c⁻¹ * c) * b := by rw [mul_assoc]
      _ = 1 * b := by rw [hcinv]
      _ = b := by simp
    rw [h1, h2] at h'
    exact h'

  have h_iff : Metric.infEDist p s_set ≤ ENNReal.ofReal δ ↔
      Metric.infEDist (f p) s'_set ≤ ENNReal.ofReal (δ / 4) := by
    rw [h_inf_scale, h5]
    constructor
    · intro h
      exact mul_le_mul_left' h c
    · intro h
      exact h_cancel h

  simpa [Metric.mem_cthickening_iff] using h_iff

/-! ========================================================================
   8. Offset bound transfer (via nearest-point property)
   ======================================================================== -/

/-- If ℓ.offset has norm ≤ 3, then (S_line ℓ).offset has norm ≤ 2.

    Uses the nearest-point property: offset(S_line ℓ) is the orthogonal
    projection of 0 onto (S_line ℓ).1, so its norm is ≤ the norm of ANY
    point in (S_line ℓ).1, including S(ℓ.offset). -/
lemma S_line_offset_bound {ℓ : AffineLine}
    (h : ‖ℓ.offset‖ ≤ 3) :
    (S_line ℓ).offset ∈ Metric.closedBall (0 : Plane) 2 := by
  let s' := (S_line ℓ).1
  have hS_offset_mem : S ℓ.offset ∈ s' :=
    (S_line_incidence ℓ.offset ℓ).mp ℓ.offset_mem
  have h_norm_min : ‖(S_line ℓ).offset‖ ≤ ‖S ℓ.offset‖ := by
    have h1 : dist (0 : Plane) (S_line ℓ).offset =
        Metric.infDist (0 : Plane) (s' : Set Plane) :=
      EuclideanGeometry.dist_orthogonalProjection_eq_infDist s' (0 : Plane)
    have h2 : Metric.infDist (0 : Plane) (s' : Set Plane) ≤
        dist (0 : Plane) (S ℓ.offset) :=
      Metric.infDist_le_dist_of_mem hS_offset_mem
    have h3 : dist (0 : Plane) (S_line ℓ).offset ≤ dist (0 : Plane) (S ℓ.offset) := by
      rw [h1] <;> exact h2
    simpa [dist_zero_right] using h3
  have h_norm_orig : ‖ℓ.offset‖ ≤ 3 := h
  have h_halfVec_le_one : ‖halfVec‖ ≤ 1 := by
    have h1 : ‖halfVec‖ ^ 2 = 1 / 2 := by
      simp [halfVec, EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> norm_num
    have h2 : 0 ≤ ‖halfVec‖ := by positivity
    nlinarith
  have h6 : ‖S ℓ.offset‖ ≤ 2 := by
    calc ‖S ℓ.offset‖
      = ‖(1 / 4 : ℝ) • ℓ.offset + halfVec‖ := by rfl
    _ ≤ ‖(1 / 4 : ℝ) • ℓ.offset‖ + ‖halfVec‖ := norm_add_le _ _
    _ = (1 / 4 : ℝ) * ‖ℓ.offset‖ + ‖halfVec‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 1 / 4 by norm_num)] <;> ring
    _ ≤ (1 / 4 : ℝ) * 3 + 1 := by gcongr
    _ = 7 / 4 := by ring
    _ ≤ 2 := by norm_num
  have h7 : ‖(S_line ℓ).offset‖ ≤ 2 := le_trans h_norm_min h6
  simpa [Metric.mem_closedBall] using h7

/-! ========================================================================
   9. S_line bi-Lipschitz bounds and S-set transfer
   ======================================================================== -/

/-- Exact offset formula for S_line:
    `(S_line ℓ).offset = ℓ.offset/4 + halfVec - P(halfVec)`
    where P is the orthogonal projection onto ℓ's direction. -/
lemma S_line_offset_formula {ℓ : AffineLine} :
    (S_line ℓ).offset = (1 / 4 : ℝ) • ℓ.offset + halfVec -
      ℓ.1.direction.starProjection halfVec := by
  let o := ℓ.offset
  let o' := (S_line ℓ).offset
  let P := ℓ.1.direction.starProjection
  have h_dir_eq : (S_line ℓ).1.direction = ℓ.1.direction := S_line_direction ℓ
  have hSo_mem : S o ∈ (S_line ℓ).1 := (S_line_incidence o ℓ).mp ℓ.offset_mem
  have h_o'_mem : o' ∈ (S_line ℓ).1 := (S_line ℓ).offset_mem
  have h_diff_dir : o' - S o ∈ (S_line ℓ).1.direction :=
    (S_line ℓ).1.vsub_mem_direction h_o'_mem hSo_mem
  have h_diff_dir' : o' - S o ∈ ℓ.1.direction := by
    rw [h_dir_eq] at h_diff_dir; exact h_diff_dir
  have hP_diff : P (o' - S o) = o' - S o :=
    (Submodule.starProjection_eq_self_iff (K := ℓ.1.direction)).mpr h_diff_dir'
  have hPo_eq_0 : P o = 0 := by
    have h : (0 : Plane) -ᵥ o ∈ ℓ.1.directionᗮ :=
      EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal ℓ.1 (0 : Plane)
    have h2 : -o ∈ ℓ.1.directionᗮ := by simpa [vsub_eq_sub] using h
    have h3 : o ∈ ℓ.1.directionᗮ := by simpa [neg_mem_iff] using h2
    exact Submodule.eq_starProjection_of_mem_orthogonal' (zero_mem ℓ.1.direction) h3 (by simp)
  have hPo'_eq_0 : P o' = 0 := by
    have h : (0 : Plane) -ᵥ o' ∈ (S_line ℓ).1.directionᗮ :=
      EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal (S_line ℓ).1 (0 : Plane)
    have h2 : -o' ∈ (S_line ℓ).1.directionᗮ := by simpa [vsub_eq_sub] using h
    have h3 : -o' ∈ ℓ.1.directionᗮ := by rw [h_dir_eq] at h2; exact h2
    have h4 : o' ∈ ℓ.1.directionᗮ := by simpa [neg_mem_iff] using h3
    exact Submodule.eq_starProjection_of_mem_orthogonal' (zero_mem ℓ.1.direction) h4 (by simp)
  have h_map_sub : P (o' - S o) = P o' - P (S o) :=
    map_sub P o' (S o)
  have h_eq : o' - S o = -P (S o) := by
    have h1 : o' - S o = P (o' - S o) := hP_diff.symm
    have h2 : P (o' - S o) = P o' - P (S o) := h_map_sub
    have h3 : o' - S o = P o' - P (S o) := by
      calc o' - S o = P (o' - S o) := h1
        _ = P o' - P (S o) := h2
    rw [hPo'_eq_0] at h3
    simpa using h3
  have h_PSo : P (S o) = P halfVec := by
    have h_So : S o = (1 / 4 : ℝ) • o + halfVec := by rfl
    rw [h_So, map_add, map_smul, hPo_eq_0, smul_zero, zero_add]
  have h_final : o' = S o - P halfVec := by
    have h : o' - S o = -P halfVec := by
      rw [h_PSo] at h_eq; exact h_eq
    have h' : o' = S o + (o' - S o) := by abel
    rw [h', h] <;> abel
  exact h_final

/-- S_line is bi-Lipschitz on AffineLine:
    lower bound 1/4, upper bound 2.
    (Direction is unchanged; offset scales by 1/4 plus a direction-dependent shift.) -/
lemma S_line_bilipschitz {ℓ₁ ℓ₂ : AffineLine} :
    (1 / 4 : ℝ) * dist ℓ₁ ℓ₂ ≤ dist (S_line ℓ₁) (S_line ℓ₂) ∧
    dist (S_line ℓ₁) (S_line ℓ₂) ≤ 2 * dist ℓ₁ ℓ₂ := by
  let P₁ := ℓ₁.1.direction.starProjection
  let P₂ := ℓ₂.1.direction.starProjection
  let o₁ := ℓ₁.offset
  let o₂ := ℓ₂.offset
  let o₁' := (S_line ℓ₁).offset
  let o₂' := (S_line ℓ₂).offset
  have h_dir1 : (S_line ℓ₁).1.direction = ℓ₁.1.direction := S_line_direction ℓ₁
  have h_dir2 : (S_line ℓ₂).1.direction = ℓ₂.1.direction := S_line_direction ℓ₂
  have h_off1 : o₁' = (1 / 4 : ℝ) • o₁ + halfVec - P₁ halfVec := S_line_offset_formula (ℓ := ℓ₁)
  have h_off2 : o₂' = (1 / 4 : ℝ) • o₂ + halfVec - P₂ halfVec := S_line_offset_formula (ℓ := ℓ₂)
  have h_halfVec_le_34 : ‖halfVec‖ ≤ 3 / 4 := by
    have h1 : ‖halfVec‖ ^ 2 = 1 / 2 := by
      simp [halfVec, EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> norm_num
    have h2 : (0 : ℝ) ≤ ‖halfVec‖ := by positivity
    nlinarith
  have h_dir_eq : ‖(S_line ℓ₁).1.direction.starProjection - (S_line ℓ₂).1.direction.starProjection‖ = ‖P₁ - P₂‖ := by
    rw [h_dir1, h_dir2]
  have h_off_diff : o₁' - o₂' = (1 / 4 : ℝ) • (o₁ - o₂) - (P₁ halfVec - P₂ halfVec) := by
    have h : o₁' - o₂' = ((1 / 4 : ℝ) • o₁ + halfVec - P₁ halfVec) - ((1 / 4 : ℝ) • o₂ + halfVec - P₂ halfVec) := by
      rw [h_off1, h_off2]
    rw [h]
    ext i
    simp [smul_sub, sub_eq_add_neg, add_assoc]
    <;> abel
  have h5 : P₁ halfVec - P₂ halfVec = (P₁ - P₂) halfVec := by
    ext i; simp [sub_apply]
  have hP_diff_bound : ‖P₁ halfVec - P₂ halfVec‖ ≤ (3 / 4 : ℝ) * ‖P₁ - P₂‖ := by
    rw [h5]
    have h6 : ‖(P₁ - P₂) halfVec‖ ≤ ‖P₁ - P₂‖ * ‖halfVec‖ :=
      ContinuousLinearMap.le_opNorm (P₁ - P₂) halfVec
    calc ‖(P₁ - P₂) halfVec‖
      ≤ ‖P₁ - P₂‖ * ‖halfVec‖ := h6
    _ ≤ ‖P₁ - P₂‖ * (3 / 4 : ℝ) := by gcongr
    _ = (3 / 4 : ℝ) * ‖P₁ - P₂‖ := by ring
  set A := ‖P₁ - P₂‖ with hA
  set B := ‖o₁ - o₂‖ with hB
  set B' := ‖o₁' - o₂'‖ with hB'
  have h_upper_off : B' ≤ B / 4 + (3 / 4 : ℝ) * A := by
    rw [hB', h_off_diff, hB, hA]
    calc ‖(1 / 4 : ℝ) • (o₁ - o₂) - (P₁ halfVec - P₂ halfVec)‖
      ≤ ‖(1 / 4 : ℝ) • (o₁ - o₂)‖ + ‖P₁ halfVec - P₂ halfVec‖ := norm_sub_le _ _
    _ = B / 4 + ‖P₁ halfVec - P₂ halfVec‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 1 / 4 by norm_num)] <;> simp [hB] <;> ring
    _ ≤ B / 4 + (3 / 4 : ℝ) * A := by gcongr
  have hA_nonneg : 0 ≤ A := by positivity
  have hB_nonneg : 0 ≤ B := by positivity
  have h_upper : dist (S_line ℓ₁) (S_line ℓ₂) ≤ 2 * dist ℓ₁ ℓ₂ := by
    have h1 : dist (S_line ℓ₁) (S_line ℓ₂) = A + B' := by
      have h_first : ‖(S_line ℓ₁).1.direction.starProjection - (S_line ℓ₂).1.direction.starProjection‖ = A := h_dir_eq
      have h_second : ‖(S_line ℓ₁).offset - (S_line ℓ₂).offset‖ = B' := by rfl
      have h_body : ‖(S_line ℓ₁).1.direction.starProjection - (S_line ℓ₂).1.direction.starProjection‖ + ‖(S_line ℓ₁).offset - (S_line ℓ₂).offset‖ = A + B' := by
        rw [h_first, h_second]
      exact h_body
    have h2 : dist ℓ₁ ℓ₂ = A + B := by rfl
    rw [h1, h2]
    linarith [h_upper_off]
  have h_inv_eq : o₁ - o₂ = (4 : ℝ) • (o₁' - o₂') + (4 : ℝ) • (P₁ halfVec - P₂ halfVec) := by
    rw [h_off_diff] <;> simp [smul_sub] <;> abel
  have h_lower_off : B ≤ 4 * B' + 3 * A := by
    rw [hB, h_inv_eq, hB', hA]
    calc ‖(4 : ℝ) • (o₁' - o₂') + (4 : ℝ) • (P₁ halfVec - P₂ halfVec)‖
      ≤ ‖(4 : ℝ) • (o₁' - o₂')‖ + ‖(4 : ℝ) • (P₁ halfVec - P₂ halfVec)‖ := norm_add_le _ _
    _ = 4 * B' + 4 * ‖P₁ halfVec - P₂ halfVec‖ := by
      rw [norm_smul, norm_smul] <;> simp [abs_of_pos (show (0 : ℝ) < 4 by norm_num), hB'] <;> ring
    _ ≤ 4 * B' + 4 * ((3 / 4 : ℝ) * A) := by gcongr
    _ = 4 * B' + 3 * A := by ring
  have h_lower : (1 / 4 : ℝ) * dist ℓ₁ ℓ₂ ≤ dist (S_line ℓ₁) (S_line ℓ₂) := by
    have h1 : dist (S_line ℓ₁) (S_line ℓ₂) = A + B' := by
      have h_first : ‖(S_line ℓ₁).1.direction.starProjection - (S_line ℓ₂).1.direction.starProjection‖ = A := h_dir_eq
      have h_second : ‖(S_line ℓ₁).offset - (S_line ℓ₂).offset‖ = B' := by rfl
      have h_body : ‖(S_line ℓ₁).1.direction.starProjection - (S_line ℓ₂).1.direction.starProjection‖ + ‖(S_line ℓ₁).offset - (S_line ℓ₂).offset‖ = A + B' := by
        rw [h_first, h_second]
      exact h_body
    have h2 : dist ℓ₁ ℓ₂ = A + B := by rfl
    rw [h1, h2]
    linarith [h_lower_off]
  exact ⟨h_lower, h_upper⟩

/-! ========================================================================
   9. Covering helper lemmas
   ======================================================================== -/

/-- Forward Lipschitz covering: `Ncover(K*ε, f '' P) ≤ Ncover(ε, P)`. -/
lemma lipschitz_forward_ncover
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {K : NNReal} (hf : LipschitzWith K f)
    {ε : ℝ} (hε_pos : 0 < ε) {P : Set X} :
    Ncover ((K : ℝ) * ε) (f '' P) ≤ Ncover ε P := by
  let ε' : NNReal := ε.toNNReal
  have hε'_pos : 0 < ε' := by
    simp [ε', hε_pos] <;> exact_mod_cast hε_pos
  have h_coe : (ε' : ℝ) = ε := by
    simp [ε', hε_pos.le]
  have h_Kε : ((K * ε' : NNReal) : ℝ) = (K : ℝ) * ε := by
    rw [NNReal.coe_mul, h_coe] <;> ring
  have h_eq : K * ε' = ((K : ℝ) * ε).toNNReal := by
    apply NNReal.coe_injective
    have hpos : 0 ≤ (K : ℝ) * ε := by positivity
    have h : (((K : ℝ) * ε).toNNReal : ℝ) = (K : ℝ) * ε := Real.coe_toNNReal _ hpos
    rw [h_Kε, h]
  have h_main : Metric.externalCoveringNumber (K * ε') (f '' P) ≤
      Metric.externalCoveringNumber ε' P :=
    externalCoveringNumber_image_lipschitz (hf := hf)
  rw [h_eq] at h_main
  simpa [Ncover] using h_main

/-- Backward antilipschitz covering: `Ncover(2*K*ε, P) ≤ Ncover(ε, f '' P)`.
    Requires `P.Nonempty`; empty case is trivial. -/
lemma antilipschitz_backward_ncover
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {K : NNReal} (hK_pos : 0 < K)
    (hf : AntilipschitzWith K f)
    {ε : ℝ} (hε_pos : 0 < ε) {P : Set X} :
    Ncover (2 * (K : ℝ) * ε) P ≤ Ncover ε (f '' P) := by
  by_cases h_empty : P = ∅
  · rw [h_empty]
    simp [Ncover, Metric.externalCoveringNumber_empty]
  · have h_nonempty : P.Nonempty := Set.nonempty_iff_ne_empty.mpr h_empty
    let ε' : NNReal := ε.toNNReal
    have hε'_pos : 0 < ε' := by
      simp [ε', hε_pos] <;> exact_mod_cast hε_pos
    have h_coe : (ε' : ℝ) = ε := by simp [ε', hε_pos.le]
    have h_fin : ∀ (x y : X), x ∈ P → y ∈ P →
        dist x y ≤ (K : ℝ) * dist (f x) (f y) := by
      intro x y _ _
      exact (antilipschitzWith_iff_le_mul_dist.mp hf) x y
    have h_Kε : ((2 * K * ε' : NNReal) : ℝ) = 2 * (K : ℝ) * ε := by
      simp [NNReal.coe_mul, h_coe] <;> ring
    have h_eq : 2 * K * ε' = (2 * (K : ℝ) * ε).toNNReal := by
      apply NNReal.coe_injective
      have hpos : 0 ≤ 2 * (K : ℝ) * ε := by positivity
      have h : (((2 * (K : ℝ) * ε).toNNReal) : ℝ) = 2 * (K : ℝ) * ε := Real.coe_toNNReal _ hpos
      rw [h_Kε, h]
    have h_main : Metric.externalCoveringNumber (2 * K * ε') P ≤
        Metric.externalCoveringNumber ε' (f '' P) :=
      externalCoveringNumber_inverse_image h_fin h_nonempty hε'_pos
    rw [h_eq] at h_main
    simpa [Ncover] using h_main

/-! ========================================================================
   10. S_line S-set transfer
   ======================================================================== -/

/-- Convert `inChart` + offset bound ≤ 2 to the bounded chart condition
    required by `affine_line_factor2_doubling`. -/
lemma boundedChart_of_inChart_offset {ℓ : AffineLine}
    (h : InStandardChart.inChart ℓ) (hoff : ‖ℓ.offset‖ ≤ 2) :
    ∃ (m b : ℝ), |m| ≤ 1 ∧ |b| ≤ 3 ∧ AffineLine.mkSlopeIntercept m b = ℓ := by
  rcases h with ⟨m, b, hm, rfl⟩
  have h_off_eq : (AffineLine.mkSlopeIntercept m b).offset = b • offsetVec m := by exact mkSlopeIntercept_offset_formula m b
  have h_norm : ‖(AffineLine.mkSlopeIntercept m b).offset‖ = |b| * ‖offsetVec m‖ := by
    rw [h_off_eq, norm_smul] <;> rfl
  have h_ov_norm : ‖offsetVec m‖ = 1 / Real.sqrt (1 + m^2) := offsetVec_norm m
  have h_m2 : m^2 ≤ 1 := by nlinarith [abs_le.mp hm]
  have h_ov_lower : ‖offsetVec m‖ ≥ 1 / Real.sqrt 2 := by
    rw [h_ov_norm]
    have h1 : 1 + m^2 ≤ 2 := by nlinarith
    have h2 : Real.sqrt (1 + m^2) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt h1
    have h3 : 0 < Real.sqrt 2 := by positivity
    have h4 : 0 < Real.sqrt (1 + m^2) := by positivity
    gcongr
  have h5 : |b| * ‖offsetVec m‖ ≤ 2 := by
    rw [h_norm] at hoff; exact hoff
  have h_pos : 0 < ‖offsetVec m‖ := by
    rw [h_ov_norm] <;> positivity
  have h6 : |b| ≤ 2 / ‖offsetVec m‖ := by
    have h_eq : |b| = (|b| * ‖offsetVec m‖) / ‖offsetVec m‖ := by
      field_simp [ne_of_gt h_pos] <;> ring
    rw [h_eq]
    gcongr
  have h7 : 2 / ‖offsetVec m‖ ≤ 2 * Real.sqrt 2 := by
    have h8 : ‖offsetVec m‖ ≥ 1 / Real.sqrt 2 := h_ov_lower
    have h9 : 0 < 1 / Real.sqrt 2 := by positivity
    have h10 : 2 / ‖offsetVec m‖ ≤ 2 / (1 / Real.sqrt 2) := by gcongr
    have h11 : 2 / (1 / Real.sqrt 2) = 2 * Real.sqrt 2 := by
      have h_sqrt2_pos : 0 < Real.sqrt 2 := by positivity
      field_simp [h_sqrt2_pos.ne'] <;> ring
    exact le_trans h10 (le_of_eq h11)
  have h12 : 2 * Real.sqrt 2 ≤ 3 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h_b : |b| ≤ 3 := by linarith
  exact ⟨m, b, hm, h_b, rfl⟩

/-- S_line is 2-Lipschitz. -/
lemma S_line_lipschitz : LipschitzWith (2 : NNReal) S_line := by
  apply LipschitzWith.of_dist_le_mul
  intro ℓ₁ ℓ₂
  exact S_line_bilipschitz.2

/-- S_line is 4-antilipschitz. -/
lemma S_line_antilipschitz : AntilipschitzWith (4 : NNReal) S_line := by
  apply AntilipschitzWith.of_le_mul_dist
  intro ℓ₁ ℓ₂
  have h := S_line_bilipschitz (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
  have h' : (1 : ℝ) / 4 * dist ℓ₁ ℓ₂ ≤ dist (S_line ℓ₁) (S_line ℓ₂) := h.1
  have h'' : dist ℓ₁ ℓ₂ ≤ (4 : ℝ) * dist (S_line ℓ₁) (S_line ℓ₂) := by
    calc dist ℓ₁ ℓ₂
      = 4 * ((1 : ℝ) / 4 * dist ℓ₁ ℓ₂) := by ring
    _ ≤ 4 * dist (S_line ℓ₁) (S_line ℓ₂) := by gcongr
  exact h''

/-- Backward covering bound: `Ncover δ F ≤ 262144 * Ncover (δ/4) (S_line '' F)`.

    Uses 4-antilipschitz (factor 2K=8, so ε=δ/8 gives scale δ) plus
    one factor-2 doubling step on the image (δ/8 → δ/4). -/
lemma S_line_ncover_backward {δ : ℝ} {F : Set AffineLine}
    (hδ_pos : 0 < δ)
    (h_chart : ∀ ℓ ∈ S_line '' F, ∃ (m b : ℝ), |m| ≤ 1 ∧ |b| ≤ 3 ∧ AffineLine.mkSlopeIntercept m b = ℓ) :
    Ncover δ F ≤ (262144 : ENNReal) * Ncover (δ / 4) (S_line '' F) := by
  set E' := S_line '' F with hE'
  have h_antilip := S_line_antilipschitz
  have h_chart' : ∀ ℓ ∈ E', ∃ (m b : ℝ), |m| ≤ 1 ∧ |b| ≤ 3 ∧ lineOfSlopeIntercept m b = ℓ := by
    intro ℓ hℓ
    rcases h_chart ℓ hℓ with ⟨m, b, hm, hb, h_eq⟩
    refine ⟨m, b, hm, hb, ?_⟩
    rw [lineOfSlopeIntercept_eq_mkSlopeIntercept m b]
    exact h_eq
  -- Step 1: antilipschitz gives Ncover(δ, F) ≤ Ncover(δ/8, E')
  have h1 : Ncover δ F ≤ Ncover (δ / 8) E' := by
    have h3 : Ncover (2 * (4 : ℝ) * (δ / 8)) F ≤ Ncover (δ / 8) E' :=
      antilipschitz_backward_ncover (hK_pos := by norm_num) h_antilip (hε_pos := by linarith) (P := F)
    have h2 : 2 * (4 : ℝ) * (δ / 8) = δ := by ring
    rw [h2] at h3
    exact h3
  -- Step 2: doubling on E': Ncover(δ/8, E') ≤ 262144 * Ncover(δ/4, E')
  have h4 : Ncover (δ / 8) E' ≤ (262144 : ENNReal) * Ncover (δ / 4) E' := by
    have h5 := affine_line_factor2_doubling (δ / 8) (by linarith) h_chart'
    have h6 : (2 * (δ / 8)).toNNReal = (δ / 4).toNNReal := by
      congr 1 <;> ring
    simpa [Ncover, h6] using h5
  exact le_trans h1 h4

/-- Chart preservation for the image: every line in S_line '' F is in the bounded chart. -/
lemma S_line_chart_image {F : Set AffineLine}
    (h_chart : ∀ ℓ ∈ F, ∃ (m b : ℝ), |m| ≤ 1 ∧ |b| ≤ 3 ∧ AffineLine.mkSlopeIntercept m b = ℓ) :
    ∀ ℓ ∈ S_line '' F, ∃ (m b : ℝ), |m| ≤ 1 ∧ |b| ≤ 3 ∧ AffineLine.mkSlopeIntercept m b = ℓ := by
  intro ℓ hℓ
  rcases hℓ with ⟨ℓ₀, hℓ₀, rfl⟩
  have h_inChart₀ : InStandardChart.inChart ℓ₀ := by
    rcases h_chart ℓ₀ hℓ₀ with ⟨m, b, hm, hb, rfl⟩
    exact ⟨m, b, hm, rfl⟩
  have h_off₀ : ‖ℓ₀.offset‖ ≤ 3 := by
    rcases h_chart ℓ₀ hℓ₀ with ⟨m, b, hm, hb, rfl⟩
    have h_off_eq : (AffineLine.mkSlopeIntercept m b).offset = b • offsetVec m :=
      mkSlopeIntercept_offset_formula m b
    have h_norm : ‖(AffineLine.mkSlopeIntercept m b).offset‖ = |b| * ‖offsetVec m‖ := by
      rw [h_off_eq, norm_smul] <;> rfl
    rw [h_norm]
    have h_ov_le_one : ‖offsetVec m‖ ≤ 1 := by
      rw [offsetVec_norm m]
      have h2 : 1 ≤ Real.sqrt (1 + m^2) := by
        have h3 : 1 ≤ 1 + m^2 := by nlinarith
        have h4 : Real.sqrt 1 ≤ Real.sqrt (1 + m^2) := Real.sqrt_le_sqrt h3
        simpa using h4
      have h_pos : 0 < Real.sqrt (1 + m^2) := by positivity
      exact (div_le_one h_pos).mpr h2
    calc |b| * ‖offsetVec m‖
      ≤ 3 * 1 := by gcongr <;> linarith
    _ = 3 := by ring
  have h_inChart : InStandardChart.inChart (S_line ℓ₀) := S_line_inChart h_inChart₀
  have h_off : ‖(S_line ℓ₀).offset‖ ≤ 2 := by
    have h := S_line_offset_bound h_off₀
    simpa [Metric.mem_closedBall] using h
  exact boundedChart_of_inChart_offset h_inChart h_off

/-- Helper: factor-2 doubling with mkSlopeIntercept chart witness. -/
lemma affine_line_factor2_doubling' (δ : ℝ) (hδ_pos : 0 < δ) (E : Set AffineLine)
    (hE : ∀ ℓ ∈ E, ∃ (m b : ℝ), |m| ≤ 1 ∧ |b| ≤ 3 ∧ AffineLine.mkSlopeIntercept m b = ℓ) :
    Ncover δ E ≤ (262144 : ENNReal) * Ncover (2 * δ) E := by
  have hE' : ∀ ℓ ∈ E, ∃ (m b : ℝ), |m| ≤ 1 ∧ |b| ≤ 3 ∧ lineOfSlopeIntercept m b = ℓ := by
    intro ℓ hℓ
    rcases hE ℓ hℓ with ⟨m, b, hm, hb, h_eq⟩
    refine ⟨m, b, hm, hb, ?_⟩
    have h_conv : lineOfSlopeIntercept m b = AffineLine.mkSlopeIntercept m b :=
      lineOfSlopeIntercept_eq_mkSlopeIntercept m b
    rw [h_conv]
    exact h_eq
  exact affine_line_factor2_doubling δ hδ_pos hE'

/-- Three-step doubling chain: Ncover(δ/4, E) ≤ 262144³ * Ncover(2δ, E). -/
lemma three_step_doubling {δ : ℝ} (hδ_pos : 0 < δ) {E : Set AffineLine}
    (h_chart : ∀ ℓ ∈ E, ∃ (m b : ℝ), |m| ≤ 1 ∧ |b| ≤ 3 ∧ AffineLine.mkSlopeIntercept m b = ℓ) :
    Ncover (δ / 4) E ≤ (262144 : ENNReal)^3 * Ncover (2 * δ) E := by
  have h1 := affine_doubling_mkSlope (δ / 4) (by linarith) E h_chart
  have h_conv1 : (2 * (δ / 4)).toNNReal = (δ / 2).toNNReal := by congr 1 <;> ring
  have h1' : Ncover (δ / 4) E ≤ (262144 : ENNReal) * Ncover (δ / 2) E := by
    simpa [Ncover, h_conv1] using h1
  have h2 := affine_doubling_mkSlope (δ / 2) (by linarith) E h_chart
  have h_conv2 : (2 * (δ / 2)).toNNReal = δ.toNNReal := by congr 1 <;> ring
  have h2' : Ncover (δ / 2) E ≤ (262144 : ENNReal) * Ncover δ E := by
    simpa [Ncover, h_conv2] using h2
  have h3 := affine_doubling_mkSlope δ hδ_pos E h_chart
  calc Ncover (δ / 4) E
    ≤ (262144 : ENNReal) * Ncover (δ / 2) E := h1'
  _ ≤ (262144 : ENNReal) * ((262144 : ENNReal) * Ncover δ E) := by gcongr
  _ = (262144 : ENNReal)^2 * Ncover δ E := by ring
  _ ≤ (262144 : ENNReal)^2 * ((262144 : ENNReal) * Ncover (2 * δ) E) := by gcongr
  _ = (262144 : ENNReal)^3 * Ncover (2 * δ) E := by ring

/-- Forward S-set transfer through S_line.

    If `F` is a `(δ, s, C)`-set of affine lines in the bounded chart,
    then `S_line '' F` is a `(δ/4, s, C')`-set with
    `C' = C * 8^s * 262144^4`.

    Proof chain for a ball B(x', r') with r' ≥ δ/4:
    1. Preimage of E' ∩ B(x', r') ⊆ F ∩ B(y₀, 8r')
    2. S-set property of F at scale δ, radius 8r'
    3. Forward Lipschitz K=2: Ncover(2δ, image) ≤ Ncover(δ, preimage)
    4. Three doubling steps on image: δ/4 → δ/2 → δ → 2δ (factor 262144³)
    5. Backward bound: Ncover(δ, F) ≤ 262144 * Ncover(δ/4, E') -/
lemma S_line_ncover_forward {δ s C : ℝ} {F : Set AffineLine}
    (hδ_pos : 0 < δ) (hs_nonneg : 0 ≤ s) (hC_pos : 0 < C)
    (h : IsDeltaSSet δ s C F)
    (h_chart : ∀ ℓ ∈ F, ∃ (m b : ℝ), |m| ≤ 1 ∧ |b| ≤ 3 ∧ AffineLine.mkSlopeIntercept m b = ℓ) :
    IsDeltaSSet (δ / 4) s (C * (8 : ℝ)^s * (262144 : ℝ)^4) (S_line '' F) := by
  set E' := S_line '' F with hE'
  have h_forward_lip := S_line_lipschitz
  have h_backward_antilip := S_line_antilipschitz
  have h_chart_image := S_line_chart_image h_chart
  rcases h with ⟨hF_nonempty, hδ_pos', hC_pos', hs_nonneg', hcover⟩
  have hE'_nonempty : E'.Nonempty := hF_nonempty.image _
  refine' ⟨hE'_nonempty, by linarith, by positivity, hs_nonneg', _⟩
  intro x' r' hr'
  let E_int := E' ∩ Metric.closedBall x' r'
  by_cases h_empty : E_int.Nonempty
  · rcases h_empty with ⟨y₀', hy₀'⟩
    rcases hy₀'.1 with ⟨y₀, hy₀F, rfl⟩
    have hy₀'_ball : dist (S_line y₀) x' ≤ r' := hy₀'.2
    let preimage : Set AffineLine := {y ∈ F | S_line y ∈ Metric.closedBall x' r'}
    have h_preimage_subset : preimage ⊆ F ∩ Metric.closedBall y₀ (8 * r') := by
      intro y hy
      have hyF : y ∈ F := hy.1
      have h_ball : dist (S_line y) x' ≤ r' := hy.2
      have h_dist : dist y y₀ ≤ 8 * r' := by
        have h1 : dist y y₀ ≤ 4 * dist (S_line y) (S_line y₀) :=
          (antilipschitzWith_iff_le_mul_dist.mp h_backward_antilip) y y₀
        have h2 : dist (S_line y) (S_line y₀) ≤
            dist (S_line y) x' + dist x' (S_line y₀) := dist_triangle _ _ _
        have h3 : dist x' (S_line y₀) = dist (S_line y₀) x' := dist_comm _ _
        linarith
      exact ⟨hyF, by simpa [Metric.mem_closedBall] using h_dist⟩
    have h_image_preimage : S_line '' preimage = E_int := by
      ext z
      simp only [hE', E_int, Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨y, ⟨hyF, hball⟩, rfl⟩
        exact ⟨⟨y, hyF, rfl⟩, hball⟩
      · rintro ⟨⟨y, hyF, rfl⟩, hball⟩
        exact ⟨y, ⟨hyF, hball⟩, rfl⟩
    have h_8r'_ge_δ : δ ≤ 8 * r' := by linarith
    have h_sset : Ncover δ (F ∩ Metric.closedBall y₀ (8 * r')) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (8 * r')) ^ s * Ncover δ F :=
      hcover y₀ (8 * r') h_8r'_ge_δ
    have h_forward : Ncover (2 * δ) E_int ≤ Ncover δ preimage := by
      rw [←h_image_preimage]
      exact lipschitz_forward_ncover h_forward_lip hδ_pos
    have h_chart_int : ∀ ℓ ∈ E_int, ∃ (m b : ℝ), |m| ≤ 1 ∧ |b| ≤ 3 ∧ AffineLine.mkSlopeIntercept m b = ℓ :=
      fun ℓ hℓ => h_chart_image ℓ (Set.mem_of_mem_inter_left hℓ)
    have h_doubling : Ncover (δ / 4) E_int ≤
        (262144 : ENNReal)^3 * Ncover (2 * δ) E_int :=
      three_step_doubling hδ_pos h_chart_int
    have h_backward : Ncover δ F ≤ (262144 : ENNReal) * Ncover (δ / 4) E' :=
      S_line_ncover_backward hδ_pos h_chart_image
    have h_mono : Ncover δ preimage ≤ Ncover δ (F ∩ Metric.closedBall y₀ (8 * r')) := by
      simpa [Ncover] using Metric.externalCoveringNumber_mono_set h_preimage_subset
    have h_posr : 0 ≤ r' := by linarith
    have h_pos8r : 0 ≤ 8 * r' := by positivity
    have h9 : (ENNReal.ofReal (8 * r')) ^ s =
        ENNReal.ofReal ((8 : ℝ)^s) * (ENNReal.ofReal r') ^ s := by
      have h1 : ENNReal.ofReal (8 * r') = ENNReal.ofReal (8 : ℝ) * ENNReal.ofReal r' := by
        rw [ENNReal.ofReal_mul (by positivity)] <;> rfl
      rw [h1]
      have h2 : (ENNReal.ofReal (8 : ℝ) * ENNReal.ofReal r') ^ s =
          (ENNReal.ofReal (8 : ℝ)) ^ s * (ENNReal.ofReal r') ^ s := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hs_nonneg]
      rw [h2]
      have h3 : (ENNReal.ofReal (8 : ℝ)) ^ s = ENNReal.ofReal ((8 : ℝ)^s) := by
        exact ENNReal.ofReal_rpow_of_nonneg (by norm_num) hs_nonneg
      rw [h3] <;> rfl
    have h11 : (262144 : ENNReal)^4 = ENNReal.ofReal ((262144 : ℝ)^4) := by norm_cast
    have h12 : ENNReal.ofReal C * ENNReal.ofReal ((8 : ℝ)^s) * ENNReal.ofReal ((262144 : ℝ)^4) =
        ENNReal.ofReal (C * (8 : ℝ)^s * (262144 : ℝ)^4) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)] <;> ring
    calc Ncover (δ / 4) E_int
      ≤ (262144 : ENNReal)^3 * Ncover (2 * δ) E_int := h_doubling
    _ ≤ (262144 : ENNReal)^3 * Ncover δ preimage := by
        exact mul_le_mul_left' h_forward _
    _ ≤ (262144 : ENNReal)^3 * Ncover δ (F ∩ Metric.closedBall y₀ (8 * r')) := by
        exact mul_le_mul_left' h_mono _
    _ ≤ (262144 : ENNReal)^3 * (ENNReal.ofReal C * (ENNReal.ofReal (8 * r')) ^ s * Ncover δ F) := by
        exact mul_le_mul_left' h_sset _
    _ ≤ (262144 : ENNReal)^3 * (ENNReal.ofReal C * (ENNReal.ofReal (8 * r')) ^ s * ((262144 : ENNReal) * Ncover (δ / 4) E')) := by
        set K_const := ENNReal.ofReal C * (ENNReal.ofReal (8 * r')) ^ s with hK_def
        have h5 : Ncover δ F ≤ (262144 : ENNReal) * Ncover (δ / 4) E' := h_backward
        have h6 : K_const * Ncover δ F ≤ K_const * ((262144 : ENNReal) * Ncover (δ / 4) E') :=
          mul_le_mul_left' h5 K_const
        have h7 : (262144 : ENNReal)^3 * (K_const * Ncover δ F) ≤
            (262144 : ENNReal)^3 * (K_const * ((262144 : ENNReal) * Ncover (δ / 4) E')) :=
          mul_le_mul_left' h6 _
        simpa [hK_def] using h7
    _ = (262144 : ENNReal)^4 * ENNReal.ofReal C * (ENNReal.ofReal (8 * r')) ^ s * Ncover (δ / 4) E' := by
        simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
    _ = ENNReal.ofReal (C * (8 : ℝ)^s * (262144 : ℝ)^4) * (ENNReal.ofReal r') ^ s * Ncover (δ / 4) E' := by
        have h14 : (262144 : ENNReal)^4 * ENNReal.ofReal C * ENNReal.ofReal ((8 : ℝ)^s) =
            ENNReal.ofReal (C * (8 : ℝ)^s * (262144 : ℝ)^4) := by
          rw [h11]
          have h_mul : ENNReal.ofReal ((262144 : ℝ)^4) * ENNReal.ofReal C * ENNReal.ofReal ((8 : ℝ)^s) =
              ENNReal.ofReal (((262144 : ℝ)^4) * C * ((8 : ℝ)^s)) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)] <;> rfl
          rw [h_mul]
          have h_real : ((262144 : ℝ)^4) * C * ((8 : ℝ)^s) = C * (8 : ℝ)^s * (262144 : ℝ)^4 := by ring
          rw [h_real]
        have h13 : (262144 : ENNReal)^4 * ENNReal.ofReal C * (ENNReal.ofReal (8 * r')) ^ s =
            ENNReal.ofReal (C * (8 : ℝ)^s * (262144 : ℝ)^4) * (ENNReal.ofReal r') ^ s := by
          rw [h9]
          have h_assoc : (262144 : ENNReal)^4 * ENNReal.ofReal C * (ENNReal.ofReal ((8 : ℝ)^s) * (ENNReal.ofReal r') ^ s) =
              ((262144 : ENNReal)^4 * ENNReal.ofReal C * ENNReal.ofReal ((8 : ℝ)^s)) * (ENNReal.ofReal r') ^ s := by
            simp [mul_assoc]
          rw [h_assoc, h14]
          <;> rfl
        rw [h13] <;> simp [mul_assoc]
  · have h_empty' : E_int = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using h_empty
    have h_goal : Ncover (δ / 4) E_int ≤
        ENNReal.ofReal (C * (8 : ℝ)^s * (262144 : ℝ)^4) * (ENNReal.ofReal r') ^ s * Ncover (δ / 4) E' := by
      rw [h_empty']
      simp [Ncover, Metric.externalCoveringNumber_empty] <;> positivity
    exact h_goal

/-! ========================================================================
   11. S0 variants: shift by (1/4,1/4) instead of (1/2,1/2)

   S0(p) = p/4 + (1/4,1/4). Maps B(0,1) into [0,1/2]² ⊂ B(0,1).
   This satisfies both unit-square indices and the ball requirement.
   ======================================================================== -/

/-- The constant vector (1/4, 1/4). -/
def quarterVec : Plane := WithLp.toLp 2 ![1 / 4, 1 / 4]

/-- Affine normalization map S0: S0(p) = p/4 + (1/4, 1/4). -/
def S0_affineMap : Plane →ᵃ[ℝ] Plane :=
  ⟨fun p => (1 / 4 : ℝ) • p + quarterVec,
   quarterScaling,
   fun p v => by
     simp [quarterScaling, smul_add] <;> abel⟩

/-- S0(p) = p/4 + (1/4, 1/4). -/
def S0 (p : Plane) : Plane := S0_affineMap p

lemma S0_apply (p : Plane) : S0 p = (1 / 4 : ℝ) • p + quarterVec := by rfl

/-- S0 scales distances by exactly 1/4. -/
lemma S0_dist (p q : Plane) : dist (S0 p) (S0 q) = (1 / 4 : ℝ) * dist p q := by
  have h1 : S0 p - S0 q = (1 / 4 : ℝ) • (p - q) := by
    simp [S0_apply, smul_sub] <;> abel
  rw [dist_eq_norm, dist_eq_norm, h1]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 1 / 4 by norm_num)] <;> ring

/-- Map an AffineLine through S0. -/
noncomputable def S0_line (ℓ : AffineLine) : AffineLine :=
  let f := S0_affineMap
  let img := AffineSubspace.map f ℓ.1
  have h_inj : Function.Injective f.linear := by
    intro x y h
    have h' : quarterScaling x = quarterScaling y := h
    have h'' : x = y := by
      simpa [quarterScaling] using congr_arg (fun z : Plane => (4 : ℝ) • z) h'
    exact h''
  let g : ℓ.1.direction →ₗ[ℝ] Plane := f.linear.comp ℓ.1.direction.subtype
  have hg_inj : Function.Injective g := by
    intro a b h
    exact Subtype.ext (h_inj h)
  let e := LinearEquiv.ofInjective g hg_inj
  have h_range : LinearMap.range g = Submodule.map f.linear ℓ.1.direction := by
    ext z
    simp [g, LinearMap.mem_range, Submodule.mem_map] <;> aesop
  have h_finrank : Module.finrank ℝ img.direction = 1 := by
    have h_dir : img.direction = Submodule.map f.linear ℓ.1.direction :=
      AffineSubspace.map_direction f ℓ.1
    rw [h_dir, ← h_range]
    exact (LinearEquiv.finrank_eq e).symm ▸ ℓ.2
  ⟨img, h_finrank⟩

lemma S0_line_subspace (ℓ : AffineLine) :
    (S0_line ℓ).1 = AffineSubspace.map S0_affineMap ℓ.1 := by rfl

lemma S0_line_set (ℓ : AffineLine) :
    ((S0_line ℓ).1 : Set Plane) = S0 '' ℓ.1 := by
  rw [S0_line_subspace] <;> rfl

lemma S0_line_incidence (p : Plane) (ℓ : AffineLine) :
    p ∈ ℓ.1 ↔ S0 p ∈ (S0_line ℓ).1 := by
  have h_set : ((S0_line ℓ).1 : Set Plane) = S0 '' (ℓ.1 : Set Plane) := S0_line_set ℓ
  have h_S0_inj : Function.Injective S0 := by
    intro x y h
    have h' : (1 / 4 : ℝ) • x + quarterVec = (1 / 4 : ℝ) • y + quarterVec := h
    have h'' : (1 / 4 : ℝ) • x = (1 / 4 : ℝ) • y := by simpa using h'
    have h3 : x = y := by
      apply_fun (fun z : Plane => (4 : ℝ) • z) at h''
      simpa using h''
    exact h3
  constructor
  · intro h; exact ⟨p, h, rfl⟩
  · intro h
    have h4 : S0 p ∈ S0 '' (ℓ.1 : Set Plane) := by
      have h5 : S0 p ∈ (S0_line ℓ).1 := h
      have h6 : ((S0_line ℓ).1 : Set Plane) = S0 '' (ℓ.1 : Set Plane) := h_set
      exact h6 ▸ h5
    rcases h4 with ⟨q, hq, h_eq⟩
    have h6 : q = p := h_S0_inj h_eq
    rw [h6] at hq
    exact hq

lemma S0_line_direction (ℓ : AffineLine) :
    (S0_line ℓ).1.direction = ℓ.1.direction := by
  have h1 : (S0_line ℓ).1.direction =
      Submodule.map S0_affineMap.linear ℓ.1.direction := by
    rw [S0_line_subspace]
    exact AffineSubspace.map_direction S0_affineMap ℓ.1
  rw [h1]
  have h2 : Submodule.map S0_affineMap.linear ℓ.1.direction = ℓ.1.direction := by
    ext z
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ℓ.1.direction.smul_mem (1 / 4 : ℝ) hx
    · intro hz
      refine ⟨(4 : ℝ) • z, ℓ.1.direction.smul_mem (4 : ℝ) hz, ?_⟩
      have h4 : S0_affineMap.linear ((4 : ℝ) • z) = z := by
        simp [S0_affineMap, quarterScaling] <;> simp [smul_smul] <;> norm_num
      exact h4
  exact h2

/-- S0 maps B(0,1) into [0,1/2]². -/
lemma S0_image_unitSquare {P : Set Plane}
    (hP_sub : P ⊆ Metric.closedBall (0 : Plane) 1) :
    ∀ p ∈ S0 '' P, 0 ≤ p 0 ∧ p 0 ≤ 1 / 2 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1 / 2 := by
  intro q hq
  rcases hq with ⟨p, hp, rfl⟩
  have hp_ball : p ∈ Metric.closedBall (0 : Plane) 1 := hP_sub hp
  have h_norm : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hp_ball
  have h0 : |p 0| ≤ 1 := by have h : |p 0| ≤ ‖p‖ := coord_abs_le_norm; linarith
  have h1 : |p 1| ≤ 1 := by have h : |p 1| ≤ ‖p‖ := coord_abs_le_norm; linarith
  have hS0 : (S0 p) 0 = p 0 / 4 + 1 / 4 := by simp [S0_apply, quarterVec] <;> ring
  have hS1 : (S0 p) 1 = p 1 / 4 + 1 / 4 := by simp [S0_apply, quarterVec] <;> ring
  have h_abs0 : -1 ≤ p 0 ∧ p 0 ≤ 1 := abs_le.mp h0
  have h_abs1 : -1 ≤ p 1 ∧ p 1 ≤ 1 := abs_le.mp h1
  refine' ⟨_, _, _, _⟩
  · rw [hS0]; linarith [h_abs0.1]
  · rw [hS0]; linarith [h_abs0.2]
  · rw [hS1]; linarith [h_abs1.1]
  · rw [hS1]; linarith [h_abs1.2]

/-- S0 maps B(0,1) into B(0,1). This is the key advantage over S. -/
lemma S0_image_ball {P : Set Plane}
    (hP_sub : P ⊆ Metric.closedBall (0 : Plane) 1) :
    S0 '' P ⊆ Metric.closedBall (0 : Plane) 1 := by
  intro q hq
  rcases hq with ⟨p, hp, rfl⟩
  have hp_ball : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hP_sub hp
  have h_qvec_norm : ‖quarterVec‖ ≤ 1 / 2 := by
    have h1 : ‖quarterVec‖ ^ 2 = 1 / 8 := by
      simp [quarterVec, EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> norm_num
    have h2 : 0 ≤ ‖quarterVec‖ := by positivity
    nlinarith
  have h_norm : ‖S0 p‖ ≤ 1 := by
    calc ‖S0 p‖
      = ‖(1 / 4 : ℝ) • p + quarterVec‖ := by rfl
    _ ≤ ‖(1 / 4 : ℝ) • p‖ + ‖quarterVec‖ := norm_add_le _ _
    _ = (1 / 4 : ℝ) * ‖p‖ + ‖quarterVec‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 1 / 4 by norm_num)] <;> ring
    _ ≤ (1 / 4 : ℝ) * 1 + 1 / 2 := by gcongr
    _ = 3 / 4 := by ring
    _ ≤ 1 := by norm_num
  simpa [Metric.mem_closedBall] using h_norm

/-- S-set transfer under S0: same constant as S. -/
lemma S0_sset {δ t C : ℝ} {P : Set Plane}
    (hP : IsDeltaSSet δ t C P) :
    IsDeltaSSet (δ / 4) t (C * (4 : ℝ)^t) (S0 '' P) := by
  have h1_raw : IsDeltaSSet ((1 / 4 : ℝ) * δ) t (C * (1 / 4 : ℝ)^(-t))
      ((fun x : Plane => (1 / 4 : ℝ) • x) '' P) :=
    rescale_sset_euclidean (c := (1 / 4 : ℝ)) (by norm_num) hP
  have hδ_eq : (1 / 4 : ℝ) * δ = δ / 4 := by ring
  have hC_eq : C * (1 / 4 : ℝ)^(-t) = C * (4 : ℝ)^t := by
    have hpos : (0 : ℝ) < 1 / 4 := by norm_num
    have h1 : (1 / 4 : ℝ)^(-t) = ((1 / 4 : ℝ)^t)⁻¹ := Real.rpow_neg (by norm_num) t
    have h2 : (1 / 4 : ℝ)^t * (4 : ℝ)^t = 1 := by
      have h3 : ((1 / 4 : ℝ) * (4 : ℝ))^t = (1 / 4 : ℝ)^t * (4 : ℝ)^t :=
        Real.mul_rpow (by norm_num) (by norm_num)
      have h4 : (1 / 4 : ℝ) * (4 : ℝ) = 1 := by norm_num
      rw [h4] at h3
      simpa using h3.symm
    have h5 : ((1 / 4 : ℝ)^t)⁻¹ = (4 : ℝ)^t := by
      exact inv_eq_of_mul_eq_one_right h2
    have h6 : (1 / 4 : ℝ)^(-t) = (4 : ℝ)^t := by
      rw [h1, h5]
    rw [h6]
  have h1 : IsDeltaSSet (δ / 4) t (C * (4 : ℝ)^t)
      ((fun x : Plane => (1 / 4 : ℝ) • x) '' P) := by
    rw [hδ_eq, hC_eq] at h1_raw; exact h1_raw
  have h2 : IsDeltaSSet (δ / 4) t (C * (4 : ℝ)^t)
      ((fun x : Plane => x + quarterVec) '' (((fun x : Plane => (1 / 4 : ℝ) • x) '' P))) :=
    translate_sset_euclidean h1
  have h3 : (fun x : Plane => x + quarterVec) '' ((fun x : Plane => (1 / 4 : ℝ) • x) '' P) = S0 '' P := by
    ext z
    simp only [S0_apply, Set.mem_image]
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, by simp [quarterVec] <;> abel⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(1 / 4 : ℝ) • x, ⟨x, hx, rfl⟩, by simp [quarterVec] <;> abel⟩
  rw [h3] at h2
  exact h2

/-- Ncover(δ/4, S0 '' P) = Ncover(δ, P). -/
lemma S0_ncover {δ : ℝ} (hδ_pos : 0 < δ) {P : Set Plane} :
    Ncover (δ / 4) (S0 '' P) = Ncover δ P := by
  let scale : Plane → Plane := fun x => (1 / 4 : ℝ) • x
  let τ : Plane → Plane := fun x => x + quarterVec
  have h1 : S0 = τ ∘ scale := by funext x; rfl
  have h_comp : S0 '' P = τ '' (scale '' P) := by
    rw [h1, Set.image_comp]
  have hδ4 : δ / 4 = (1 / 4 : ℝ) * δ := by ring
  have h_scale_eq : Ncover (δ / 4) (scale '' P) = Ncover δ P := by
    rw [hδ4]
    exact ncover_scale (show (0 : ℝ) < 1 / 4 by norm_num) (by norm_num) hδ_pos
  have h_scale_eq' : Metric.externalCoveringNumber (δ / 4).toNNReal (scale '' P) =
      Metric.externalCoveringNumber δ.toNNReal P := by
    simpa [Ncover] using h_scale_eq
  have h_translate : Metric.externalCoveringNumber (δ / 4).toNNReal (τ '' (scale '' P)) =
      Metric.externalCoveringNumber (δ / 4).toNNReal (scale '' P) :=
    ncover_translate (ε := (δ / 4).toNNReal) (P := scale '' P) (v := quarterVec)
  have h_main : Metric.externalCoveringNumber (δ / 4).toNNReal (S0 '' P) =
      Metric.externalCoveringNumber δ.toNNReal P := by
    calc Metric.externalCoveringNumber (δ / 4).toNNReal (S0 '' P)
      = Metric.externalCoveringNumber (δ / 4).toNNReal (τ '' (scale '' P)) := by rw [h_comp]
    _ = Metric.externalCoveringNumber (δ / 4).toNNReal (scale '' P) := h_translate
    _ = Metric.externalCoveringNumber δ.toNNReal P := h_scale_eq'
  simpa [Ncover] using h_main

/-- Incidence transfer for S0. -/
lemma S0_incidence {δ : ℝ} (hδ : 0 ≤ δ) {p : Plane} {ℓ : AffineLine} :
    p ∈ Metric.cthickening δ ℓ.1 ↔
    S0 p ∈ Metric.cthickening (δ / 4) (S0_line ℓ).1 := by
  let f := S0
  let s_set : Set Plane := ℓ.1
  let s'_set : Set Plane := (S0_line ℓ).1
  have h_set_eq : (s'_set : Set Plane) = f '' s_set := S0_line_set ℓ
  let c : ENNReal := ENNReal.ofReal (1 / 4 : ℝ)
  have hc_pos : c ≠ 0 := by simp [c] <;> norm_num
  have hc_top : c ≠ ⊤ := by simp [c] <;> norm_num
  have h_edist_scale : ∀ (x y : Plane), edist (f x) (f y) = c * edist x y := by
    intro x y
    have h1 : edist (f x) (f y) = ENNReal.ofReal (dist (f x) (f y)) := by rw [edist_dist]
    rw [h1, edist_dist]
    have h2 : dist (f x) (f y) = (1 / 4 : ℝ) * dist x y := S0_dist x y
    rw [h2]
    have h3 : ENNReal.ofReal ((1 / 4 : ℝ) * dist x y) = c * ENNReal.ofReal (dist x y) := by
      have h_pos : (0 : ℝ) ≤ 1 / 4 := by norm_num
      rw [ENNReal.ofReal_mul h_pos] <;> rfl
    rw [h3]
  let y0_sub := EuclideanGeometry.orthogonalProjection ℓ.1 p
  let y0 : Plane := (y0_sub : Plane)
  have hy0_mem : y0 ∈ s_set := y0_sub.prop
  have h_nearest : dist p y0 = Metric.infDist p s_set :=
    EuclideanGeometry.dist_orthogonalProjection_eq_infDist ℓ.1 p
  have h_infEDist_eq : Metric.infEDist p s_set = edist p y0 := by
    have h1 : ∀ y ∈ s_set, edist p y0 ≤ edist p y := by
      intro y hy
      have h2 : dist p y0 ≤ dist p y := by
        rw [h_nearest]; exact Metric.infDist_le_dist_of_mem hy
      have h2' : edist p y0 ≤ edist p y := by
        rw [edist_dist, edist_dist]; exact ENNReal.ofReal_le_ofReal h2
      exact h2'
    have h3 : Metric.infEDist p s_set ≤ edist p y0 := Metric.infEDist_le_edist_of_mem hy0_mem
    have h4 : edist p y0 ≤ Metric.infEDist p s_set := Metric.le_infEDist.mpr h1
    exact le_antisymm h3 h4
  have h_upper : Metric.infEDist (f p) s'_set ≤ c * Metric.infEDist p s_set := by
    rw [h_infEDist_eq]
    have h5 : f y0 ∈ s'_set := by rw [h_set_eq]; exact ⟨y0, hy0_mem, rfl⟩
    have h6 : Metric.infEDist (f p) s'_set ≤ edist (f p) (f y0) :=
      Metric.infEDist_le_edist_of_mem h5
    rw [h_edist_scale p y0] at h6; exact h6
  have h_lower : c * Metric.infEDist p s_set ≤ Metric.infEDist (f p) s'_set := by
    rw [h_set_eq]
    apply Metric.le_infEDist.mpr
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    have h7 : Metric.infEDist p s_set ≤ edist p y := Metric.infEDist_le_edist_of_mem hy
    have h8 : c * Metric.infEDist p s_set ≤ c * edist p y := mul_le_mul_left' h7 c
    rw [h_edist_scale p y]; exact h8
  have h_inf_scale : Metric.infEDist (f p) s'_set = c * Metric.infEDist p s_set :=
    le_antisymm h_upper h_lower
  have h5 : ENNReal.ofReal (δ / 4) = c * ENNReal.ofReal δ := by
    have h : ENNReal.ofReal (δ * (1 / 4 : ℝ)) = ENNReal.ofReal δ * c := by
      rw [ENNReal.ofReal_mul hδ] <;> rfl
    have h2 : δ / 4 = δ * (1 / 4 : ℝ) := by ring
    rw [h2, h] <;> ring
  have h_cancel : ∀ {a b : ENNReal}, c * a ≤ c * b → a ≤ b := by
    intro a b h
    have hcinv : c⁻¹ * c = 1 := by
      rw [mul_comm]; exact ENNReal.mul_inv_cancel hc_pos hc_top
    have h' : c⁻¹ * (c * a) ≤ c⁻¹ * (c * b) := mul_le_mul_left' h c⁻¹
    have h1 : c⁻¹ * (c * a) = a := by
      rw [←mul_assoc, hcinv, one_mul]
    have h2 : c⁻¹ * (c * b) = b := by
      rw [←mul_assoc, hcinv, one_mul]
    rw [h1, h2] at h'
    exact h'
  have h_iff : Metric.infEDist p s_set ≤ ENNReal.ofReal δ ↔
      Metric.infEDist (f p) s'_set ≤ ENNReal.ofReal (δ / 4) := by
    rw [h_inf_scale, h5]
    constructor
    · intro h; exact mul_le_mul_left' h c
    · intro h; exact h_cancel h
  simpa [Metric.mem_cthickening_iff] using h_iff

/-- Exact offset formula for S0_line. -/
lemma S0_line_offset_formula {ℓ : AffineLine} :
    (S0_line ℓ).offset = (1 / 4 : ℝ) • ℓ.offset + quarterVec -
      ℓ.1.direction.starProjection quarterVec := by
  let o := ℓ.offset
  let o' := (S0_line ℓ).offset
  let P := ℓ.1.direction.starProjection
  have h_dir_eq : (S0_line ℓ).1.direction = ℓ.1.direction := S0_line_direction ℓ
  have hSo_mem : S0 o ∈ (S0_line ℓ).1 := (S0_line_incidence o ℓ).mp ℓ.offset_mem
  have h_o'_mem : o' ∈ (S0_line ℓ).1 := (S0_line ℓ).offset_mem
  have h_diff_dir : o' - S0 o ∈ (S0_line ℓ).1.direction :=
    (S0_line ℓ).1.vsub_mem_direction h_o'_mem hSo_mem
  have h_diff_dir' : o' - S0 o ∈ ℓ.1.direction := by
    rw [h_dir_eq] at h_diff_dir; exact h_diff_dir
  have hP_diff : P (o' - S0 o) = o' - S0 o :=
    Submodule.eq_starProjection_of_mem_orthogonal'
      (u := o' - S0 o) (v := o' - S0 o) (z := (0 : Plane))
      h_diff_dir' (zero_mem ℓ.1.directionᗮ) (by simp)
  have hPo_eq_0 : P o = 0 := by
    have h : (0 : Plane) -ᵥ o ∈ ℓ.1.directionᗮ :=
      EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal ℓ.1 (0 : Plane)
    have h2 : -o ∈ ℓ.1.directionᗮ := by simpa [vsub_eq_sub] using h
    have h3 : o ∈ ℓ.1.directionᗮ := by simpa [neg_mem_iff] using h2
    exact Submodule.eq_starProjection_of_mem_orthogonal'
      (u := o) (v := (0 : Plane)) (z := o)
      (zero_mem ℓ.1.direction) h3 (by simp)
  have hPo'_eq_0 : P o' = 0 := by
    have h : (0 : Plane) -ᵥ o' ∈ (S0_line ℓ).1.directionᗮ :=
      EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal (S0_line ℓ).1 (0 : Plane)
    have h2 : -o' ∈ (S0_line ℓ).1.directionᗮ := by simpa [vsub_eq_sub] using h
    have h3 : -o' ∈ ℓ.1.directionᗮ := by rw [h_dir_eq] at h2; exact h2
    have h4 : o' ∈ ℓ.1.directionᗮ := by simpa [neg_mem_iff] using h3
    exact Submodule.eq_starProjection_of_mem_orthogonal'
      (u := o') (v := (0 : Plane)) (z := o')
      (zero_mem ℓ.1.direction) h4 (by simp)
  have h_map_sub : P (o' - S0 o) = P o' - P (S0 o) :=
    map_sub P o' (S0 o)
  have h_eq : o' - S0 o = -P (S0 o) := by
    have h1 : o' - S0 o = P (o' - S0 o) := hP_diff.symm
    have h2 : P (o' - S0 o) = P o' - P (S0 o) := h_map_sub
    have h3 : o' - S0 o = P o' - P (S0 o) := by
      calc o' - S0 o = P (o' - S0 o) := h1
        _ = P o' - P (S0 o) := h2
    rw [hPo'_eq_0] at h3
    simpa using h3
  have h_PSo : P (S0 o) = P quarterVec := by
    have h_So : S0 o = (1 / 4 : ℝ) • o + quarterVec := by rfl
    rw [h_So, map_add, map_smul, hPo_eq_0, smul_zero, zero_add]
  have h_final : o' = S0 o - P quarterVec := by
    have h : o' - S0 o = -P quarterVec := by
      rw [h_PSo] at h_eq; exact h_eq
    have h' : o' = S0 o + (o' - S0 o) := by abel
    rw [h', h] <;> abel
  exact h_final

/-- S0_line is bi-Lipschitz: lower bound 1/4, upper bound 2. -/
lemma S0_line_bilipschitz {ℓ₁ ℓ₂ : AffineLine} :
    (1 / 4 : ℝ) * dist ℓ₁ ℓ₂ ≤ dist (S0_line ℓ₁) (S0_line ℓ₂) ∧
    dist (S0_line ℓ₁) (S0_line ℓ₂) ≤ 2 * dist ℓ₁ ℓ₂ := by
  let P₁ := ℓ₁.1.direction.starProjection
  let P₂ := ℓ₂.1.direction.starProjection
  let o₁ := ℓ₁.offset
  let o₂ := ℓ₂.offset
  let o₁' := (S0_line ℓ₁).offset
  let o₂' := (S0_line ℓ₂).offset
  have h_dir1 : (S0_line ℓ₁).1.direction = ℓ₁.1.direction := S0_line_direction ℓ₁
  have h_dir2 : (S0_line ℓ₂).1.direction = ℓ₂.1.direction := S0_line_direction ℓ₂
  have h_off1 : o₁' = (1 / 4 : ℝ) • o₁ + quarterVec - P₁ quarterVec := S0_line_offset_formula (ℓ := ℓ₁)
  have h_off2 : o₂' = (1 / 4 : ℝ) • o₂ + quarterVec - P₂ quarterVec := S0_line_offset_formula (ℓ := ℓ₂)
  have h_qvec_le_34 : ‖quarterVec‖ ≤ 3 / 4 := by
    have h1 : ‖quarterVec‖ ^ 2 = 1 / 8 := by
      simp [quarterVec, EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> norm_num
    have h2 : (0 : ℝ) ≤ ‖quarterVec‖ := by positivity
    nlinarith
  have h_dir_eq : ‖(S0_line ℓ₁).1.direction.starProjection - (S0_line ℓ₂).1.direction.starProjection‖ = ‖P₁ - P₂‖ := by
    rw [h_dir1, h_dir2]
  have h_off_diff : o₁' - o₂' = (1 / 4 : ℝ) • (o₁ - o₂) - (P₁ quarterVec - P₂ quarterVec) := by
    have h : o₁' - o₂' = ((1 / 4 : ℝ) • o₁ + quarterVec - P₁ quarterVec) - ((1 / 4 : ℝ) • o₂ + quarterVec - P₂ quarterVec) := by
      rw [h_off1, h_off2]
    rw [h]
    ext i
    simp [smul_sub, sub_eq_add_neg, add_assoc]
    <;> abel
  have h5 : P₁ quarterVec - P₂ quarterVec = (P₁ - P₂) quarterVec := by
    ext i; simp [sub_apply]
  have hP_diff_bound : ‖P₁ quarterVec - P₂ quarterVec‖ ≤ (3 / 4 : ℝ) * ‖P₁ - P₂‖ := by
    rw [h5]
    have h6 : ‖(P₁ - P₂) quarterVec‖ ≤ ‖P₁ - P₂‖ * ‖quarterVec‖ :=
      ContinuousLinearMap.le_opNorm (P₁ - P₂) quarterVec
    calc ‖(P₁ - P₂) quarterVec‖
      ≤ ‖P₁ - P₂‖ * ‖quarterVec‖ := h6
    _ ≤ ‖P₁ - P₂‖ * (3 / 4 : ℝ) := by gcongr
    _ = (3 / 4 : ℝ) * ‖P₁ - P₂‖ := by ring
  set A := ‖P₁ - P₂‖ with hA
  set B := ‖o₁ - o₂‖ with hB
  set B' := ‖o₁' - o₂'‖ with hB'
  have h_upper_off : B' ≤ B / 4 + (3 / 4 : ℝ) * A := by
    rw [hB', h_off_diff, hB, hA]
    calc ‖(1 / 4 : ℝ) • (o₁ - o₂) - (P₁ quarterVec - P₂ quarterVec)‖
      ≤ ‖(1 / 4 : ℝ) • (o₁ - o₂)‖ + ‖P₁ quarterVec - P₂ quarterVec‖ := norm_sub_le _ _
    _ = B / 4 + ‖P₁ quarterVec - P₂ quarterVec‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 1 / 4 by norm_num)] <;> simp [hB] <;> ring
    _ ≤ B / 4 + (3 / 4 : ℝ) * A := by gcongr
  have hA_nonneg : 0 ≤ A := by positivity
  have hB_nonneg : 0 ≤ B := by positivity
  have h_upper : dist (S0_line ℓ₁) (S0_line ℓ₂) ≤ 2 * dist ℓ₁ ℓ₂ := by
    have h1 : dist (S0_line ℓ₁) (S0_line ℓ₂) = A + B' := by
      have h_first : ‖(S0_line ℓ₁).1.direction.starProjection - (S0_line ℓ₂).1.direction.starProjection‖ = A := h_dir_eq
      have h_second : ‖(S0_line ℓ₁).offset - (S0_line ℓ₂).offset‖ = B' := by rfl
      have h_body : ‖(S0_line ℓ₁).1.direction.starProjection - (S0_line ℓ₂).1.direction.starProjection‖ + ‖(S0_line ℓ₁).offset - (S0_line ℓ₂).offset‖ = A + B' := by
        rw [h_first, h_second]
      exact h_body
    have h2 : dist ℓ₁ ℓ₂ = A + B := by rfl
    rw [h1, h2]
    linarith [h_upper_off]
  have h_inv_eq : o₁ - o₂ = (4 : ℝ) • (o₁' - o₂') + (4 : ℝ) • (P₁ quarterVec - P₂ quarterVec) := by
    rw [h_off_diff] <;> simp [smul_sub] <;> abel
  have h_lower_off : B ≤ 4 * B' + 3 * A := by
    rw [hB, h_inv_eq, hB', hA]
    calc ‖(4 : ℝ) • (o₁' - o₂') + (4 : ℝ) • (P₁ quarterVec - P₂ quarterVec)‖
      ≤ ‖(4 : ℝ) • (o₁' - o₂')‖ + ‖(4 : ℝ) • (P₁ quarterVec - P₂ quarterVec)‖ := norm_add_le _ _
    _ = 4 * B' + 4 * ‖P₁ quarterVec - P₂ quarterVec‖ := by
      rw [norm_smul, norm_smul] <;> simp [abs_of_pos (show (0 : ℝ) < 4 by norm_num), hB'] <;> ring
    _ ≤ 4 * B' + 4 * ((3 / 4 : ℝ) * A) := by gcongr
    _ = 4 * B' + 3 * A := by ring
  have h_lower : (1 / 4 : ℝ) * dist ℓ₁ ℓ₂ ≤ dist (S0_line ℓ₁) (S0_line ℓ₂) := by
    have h1 : dist (S0_line ℓ₁) (S0_line ℓ₂) = A + B' := by
      have h_first : ‖(S0_line ℓ₁).1.direction.starProjection - (S0_line ℓ₂).1.direction.starProjection‖ = A := h_dir_eq
      have h_second : ‖(S0_line ℓ₁).offset - (S0_line ℓ₂).offset‖ = B' := by rfl
      have h_body : ‖(S0_line ℓ₁).1.direction.starProjection - (S0_line ℓ₂).1.direction.starProjection‖ + ‖(S0_line ℓ₁).offset - (S0_line ℓ₂).offset‖ = A + B' := by
        rw [h_first, h_second]
      exact h_body
    have h2 : dist ℓ₁ ℓ₂ = A + B := by rfl
    rw [h1, h2]
    linarith [h_lower_off]
  exact ⟨h_lower, h_upper⟩

/-- S0_line chart preservation. -/
lemma S0_line_inChart {ℓ : AffineLine} (h : InStandardChart.inChart ℓ) :
    InStandardChart.inChart (S0_line ℓ) := by
  rcases h with ⟨m, b, hm_bound, rfl⟩
  let q : Plane := S0 (AffineLine.mkSlopeIntercept m b).offset
  have hq_in : q ∈ (S0_line (AffineLine.mkSlopeIntercept m b)).1 :=
    (S0_line_incidence (AffineLine.mkSlopeIntercept m b).offset
      (AffineLine.mkSlopeIntercept m b)).mp
      (AffineLine.offset_mem (AffineLine.mkSlopeIntercept m b))
  let b' : ℝ := q 1 - m * q 0
  have h_dir_eq : (S0_line (AffineLine.mkSlopeIntercept m b)).1.direction =
      (AffineLine.mkSlopeIntercept m b').1.direction := by
    have h1 : (S0_line (AffineLine.mkSlopeIntercept m b)).1.direction =
        (AffineLine.mkSlopeIntercept m b).1.direction :=
      S0_line_direction (AffineLine.mkSlopeIntercept m b)
    rw [h1]
    have h2 : (AffineLine.mkSlopeIntercept m b).1.direction =
        (AffineLine.mkSlopeIntercept m b').1.direction := by
      simp [AffineLine.mkSlopeIntercept] <;> rfl
    exact h2
  have h_common : q ∈ (S0_line (AffineLine.mkSlopeIntercept m b)).1 ∧
      q ∈ (AffineLine.mkSlopeIntercept m b').1 := by
    constructor
    · exact hq_in
    · rw [mkSlopeIntercept_mem_iff]
      simp [b'] <;> ring
  have h_eq : (S0_line (AffineLine.mkSlopeIntercept m b)).1 =
      (AffineLine.mkSlopeIntercept m b').1 :=
    AffineSubspace.ext_of_direction_eq h_dir_eq ⟨q, h_common.1, h_common.2⟩
  have h_line_eq : S0_line (AffineLine.mkSlopeIntercept m b) =
      AffineLine.mkSlopeIntercept m b' := by
    apply Subtype.ext
    exact h_eq
  rw [h_line_eq]
  exact ⟨m, b', hm_bound, rfl⟩

/-- S0_line offset bound: if ‖ℓ.offset‖ ≤ 3, then ‖(S0_line ℓ).offset‖ ≤ 2. -/
lemma S0_line_offset_bound {ℓ : AffineLine}
    (h : ‖ℓ.offset‖ ≤ 3) :
    (S0_line ℓ).offset ∈ Metric.closedBall (0 : Plane) 2 := by
  let s' := (S0_line ℓ).1
  have hS_offset_mem : S0 ℓ.offset ∈ s' :=
    (S0_line_incidence ℓ.offset ℓ).mp ℓ.offset_mem
  have h_norm_min : ‖(S0_line ℓ).offset‖ ≤ ‖S0 ℓ.offset‖ := by
    have h1 : dist (0 : Plane) (S0_line ℓ).offset =
        Metric.infDist (0 : Plane) (s' : Set Plane) :=
      EuclideanGeometry.dist_orthogonalProjection_eq_infDist s' (0 : Plane)
    have h2 : Metric.infDist (0 : Plane) (s' : Set Plane) ≤
        dist (0 : Plane) (S0 ℓ.offset) :=
      Metric.infDist_le_dist_of_mem hS_offset_mem
    have h3 : dist (0 : Plane) (S0_line ℓ).offset ≤ dist (0 : Plane) (S0 ℓ.offset) := by
      rw [h1] <;> exact h2
    simpa [dist_zero_right] using h3
  have h_norm_orig : ‖ℓ.offset‖ ≤ 3 := h
  have h_qvec_le_one : ‖quarterVec‖ ≤ 1 := by
    have h1 : ‖quarterVec‖ ^ 2 = 1 / 8 := by
      simp [quarterVec, EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> norm_num
    nlinarith [norm_nonneg quarterVec]
  have h6 : ‖S0 ℓ.offset‖ ≤ 2 := by
    calc ‖S0 ℓ.offset‖
      = ‖(1 / 4 : ℝ) • ℓ.offset + quarterVec‖ := by rfl
    _ ≤ ‖(1 / 4 : ℝ) • ℓ.offset‖ + ‖quarterVec‖ := norm_add_le _ _
    _ = (1 / 4 : ℝ) * ‖ℓ.offset‖ + ‖quarterVec‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 1 / 4 by norm_num)] <;> ring
    _ ≤ (1 / 4 : ℝ) * 3 + 1 := by gcongr
    _ = 7 / 4 := by ring
    _ ≤ 2 := by norm_num
  have h7 : ‖(S0_line ℓ).offset‖ ≤ 2 := le_trans h_norm_min h6
  simpa [Metric.mem_closedBall] using h7

/-- S0_line is 2-Lipschitz. -/
lemma S0_line_lipschitz : LipschitzWith (2 : NNReal) S0_line := by
  apply LipschitzWith.of_dist_le_mul
  intro ℓ₁ ℓ₂
  exact S0_line_bilipschitz.2

/-- S0_line is 4-antilipschitz. -/
lemma S0_line_antilipschitz : AntilipschitzWith (4 : NNReal) S0_line := by
  apply AntilipschitzWith.of_le_mul_dist
  intro ℓ₁ ℓ₂
  have h := S0_line_bilipschitz (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
  have h' : (1 : ℝ) / 4 * dist ℓ₁ ℓ₂ ≤ dist (S0_line ℓ₁) (S0_line ℓ₂) := h.1
  have h'' : dist ℓ₁ ℓ₂ ≤ (4 : ℝ) * dist (S0_line ℓ₁) (S0_line ℓ₂) := by
    calc dist ℓ₁ ℓ₂
      = 4 * ((1 : ℝ) / 4 * dist ℓ₁ ℓ₂) := by ring
    _ ≤ 4 * dist (S0_line ℓ₁) (S0_line ℓ₂) := by gcongr
  exact h''

/-- Backward covering bound for S0_line. -/
lemma S0_line_ncover_backward {δ : ℝ} {F : Set AffineLine}
    (hδ_pos : 0 < δ)
    (h_chart : ∀ ℓ ∈ S0_line '' F, ∃ (m b : ℝ), |m| ≤ 1 ∧ |b| ≤ 3 ∧ AffineLine.mkSlopeIntercept m b = ℓ) :
    Ncover δ F ≤ (262144 : ENNReal) * Ncover (δ / 4) (S0_line '' F) := by
  set E' := S0_line '' F with hE'
  have h_antilip := S0_line_antilipschitz
  have h_chart' : ∀ ℓ ∈ E', ∃ (m b : ℝ), |m| ≤ 1 ∧ |b| ≤ 3 ∧ lineOfSlopeIntercept m b = ℓ := by
    intro ℓ hℓ
    rcases h_chart ℓ hℓ with ⟨m, b, hm, hb, h_eq⟩
    refine ⟨m, b, hm, hb, ?_⟩
    rw [lineOfSlopeIntercept_eq_mkSlopeIntercept m b]
    exact h_eq
  have h1 : Ncover δ F ≤ Ncover (δ / 8) E' := by
    have h3 : Ncover (2 * (4 : ℝ) * (δ / 8)) F ≤ Ncover (δ / 8) E' :=
      antilipschitz_backward_ncover (hK_pos := by norm_num) h_antilip (hε_pos := by linarith) (P := F)
    have h2 : 2 * (4 : ℝ) * (δ / 8) = δ := by ring
    rw [h2] at h3
    exact h3
  have h4 : Ncover (δ / 8) E' ≤ (262144 : ENNReal) * Ncover (δ / 4) E' := by
    have h5 := affine_line_factor2_doubling (δ / 8) (by linarith) h_chart'
    have h6 : (2 * (δ / 8)).toNNReal = (δ / 4).toNNReal := by
      congr 1 <;> ring
    simpa [Ncover, h6] using h5
  exact le_trans h1 h4

/-- Chart image for S0_line. -/
lemma S0_line_chart_image {F : Set AffineLine}
    (h_chart : ∀ ℓ ∈ F, ∃ (m b : ℝ), |m| ≤ 1 ∧ |b| ≤ 3 ∧ AffineLine.mkSlopeIntercept m b = ℓ) :
    ∀ ℓ ∈ S0_line '' F, ∃ (m b : ℝ), |m| ≤ 1 ∧ |b| ≤ 3 ∧ AffineLine.mkSlopeIntercept m b = ℓ := by
  intro ℓ hℓ
  rcases hℓ with ⟨ℓ₀, hℓ₀, rfl⟩
  have h_inChart₀ : InStandardChart.inChart ℓ₀ := by
    rcases h_chart ℓ₀ hℓ₀ with ⟨m, b, hm, hb, rfl⟩
    exact ⟨m, b, hm, rfl⟩
  have h_off₀ : ‖ℓ₀.offset‖ ≤ 3 := by
    rcases h_chart ℓ₀ hℓ₀ with ⟨m, b, hm, hb, rfl⟩
    have h_off_eq : (AffineLine.mkSlopeIntercept m b).offset = b • offsetVec m :=
      mkSlopeIntercept_offset_formula m b
    have h_norm : ‖(AffineLine.mkSlopeIntercept m b).offset‖ = |b| * ‖offsetVec m‖ := by
      rw [h_off_eq, norm_smul] <;> rfl
    rw [h_norm]
    have h_ov_le_one : ‖offsetVec m‖ ≤ 1 := by
      rw [offsetVec_norm m]
      have h2 : 1 ≤ Real.sqrt (1 + m^2) := by
        have h3 : 1 ≤ 1 + m^2 := by nlinarith
        have h4 : Real.sqrt 1 ≤ Real.sqrt (1 + m^2) := Real.sqrt_le_sqrt h3
        simpa using h4
      have h_pos : 0 < Real.sqrt (1 + m^2) := by positivity
      exact (div_le_one h_pos).mpr h2
    calc |b| * ‖offsetVec m‖
      ≤ 3 * 1 := by gcongr <;> linarith
    _ = 3 := by ring
  have h_inChart : InStandardChart.inChart (S0_line ℓ₀) := S0_line_inChart h_inChart₀
  have h_off : ‖(S0_line ℓ₀).offset‖ ≤ 2 := by
    have h := S0_line_offset_bound h_off₀
    simpa [Metric.mem_closedBall] using h
  exact boundedChart_of_inChart_offset h_inChart h_off

/-- Forward S-set transfer through S0_line. Same constant as S_line. -/
lemma S0_line_ncover_forward {δ s C : ℝ} {F : Set AffineLine}
    (hδ_pos : 0 < δ) (hs_nonneg : 0 ≤ s) (hC_pos : 0 < C)
    (h : IsDeltaSSet δ s C F)
    (h_chart : ∀ ℓ ∈ F, ∃ (m b : ℝ), |m| ≤ 1 ∧ |b| ≤ 3 ∧ AffineLine.mkSlopeIntercept m b = ℓ) :
    IsDeltaSSet (δ / 4) s (C * (8 : ℝ)^s * (262144 : ℝ)^4) (S0_line '' F) := by
  set E' := S0_line '' F with hE'
  have h_forward_lip := S0_line_lipschitz
  have h_backward_antilip := S0_line_antilipschitz
  have h_chart_image := S0_line_chart_image h_chart
  rcases h with ⟨hF_nonempty, hδ_pos', hC_pos', hs_nonneg', hcover⟩
  have hE'_nonempty : E'.Nonempty := hF_nonempty.image _
  refine' ⟨hE'_nonempty, by linarith, by positivity, hs_nonneg', _⟩
  intro x' r' hr'
  let E_int := E' ∩ Metric.closedBall x' r'
  by_cases h_empty : E_int.Nonempty
  · rcases h_empty with ⟨y₀', hy₀'⟩
    rcases hy₀'.1 with ⟨y₀, hy₀F, rfl⟩
    have hy₀'_ball : dist (S0_line y₀) x' ≤ r' := hy₀'.2
    let preimage : Set AffineLine := {y ∈ F | S0_line y ∈ Metric.closedBall x' r'}
    have h_preimage_subset : preimage ⊆ F ∩ Metric.closedBall y₀ (8 * r') := by
      intro y hy
      have hyF : y ∈ F := hy.1
      have h_ball : dist (S0_line y) x' ≤ r' := hy.2
      have h_dist : dist y y₀ ≤ 8 * r' := by
        have h1 : dist y y₀ ≤ 4 * dist (S0_line y) (S0_line y₀) :=
          (antilipschitzWith_iff_le_mul_dist.mp h_backward_antilip) y y₀
        have h2 : dist (S0_line y) (S0_line y₀) ≤
            dist (S0_line y) x' + dist x' (S0_line y₀) := dist_triangle _ _ _
        have h3 : dist x' (S0_line y₀) = dist (S0_line y₀) x' := dist_comm _ _
        linarith
      exact ⟨hyF, by simpa [Metric.mem_closedBall] using h_dist⟩
    have h_image_preimage : S0_line '' preimage = E_int := by
      ext z
      simp only [hE', E_int, Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨y, ⟨hyF, hball⟩, rfl⟩
        exact ⟨⟨y, hyF, rfl⟩, hball⟩
      · rintro ⟨⟨y, hyF, rfl⟩, hball⟩
        exact ⟨y, ⟨hyF, hball⟩, rfl⟩
    have h_8r'_ge_δ : δ ≤ 8 * r' := by linarith
    have h_sset : Ncover δ (F ∩ Metric.closedBall y₀ (8 * r')) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (8 * r')) ^ s * Ncover δ F :=
      hcover y₀ (8 * r') h_8r'_ge_δ
    have h_forward : Ncover (2 * δ) E_int ≤ Ncover δ preimage := by
      rw [←h_image_preimage]
      exact lipschitz_forward_ncover h_forward_lip hδ_pos
    have h_chart_int : ∀ ℓ ∈ E_int, ∃ (m b : ℝ), |m| ≤ 1 ∧ |b| ≤ 3 ∧ AffineLine.mkSlopeIntercept m b = ℓ :=
      fun ℓ hℓ => h_chart_image ℓ (Set.mem_of_mem_inter_left hℓ)
    have h_doubling : Ncover (δ / 4) E_int ≤
        (262144 : ENNReal)^3 * Ncover (2 * δ) E_int :=
      three_step_doubling hδ_pos h_chart_int
    have h_backward : Ncover δ F ≤ (262144 : ENNReal) * Ncover (δ / 4) E' :=
      S0_line_ncover_backward hδ_pos h_chart_image
    have h_mono : Ncover δ preimage ≤ Ncover δ (F ∩ Metric.closedBall y₀ (8 * r')) := by
      simpa [Ncover] using Metric.externalCoveringNumber_mono_set h_preimage_subset
    have h_posr : 0 ≤ r' := by linarith
    have h_pos8r : 0 ≤ 8 * r' := by positivity
    have h9 : (ENNReal.ofReal (8 * r')) ^ s =
        ENNReal.ofReal ((8 : ℝ)^s) * (ENNReal.ofReal r') ^ s := by
      have h1 : ENNReal.ofReal (8 * r') = ENNReal.ofReal (8 : ℝ) * ENNReal.ofReal r' := by
        rw [ENNReal.ofReal_mul (by positivity)] <;> rfl
      rw [h1]
      have h2 : (ENNReal.ofReal (8 : ℝ) * ENNReal.ofReal r') ^ s =
          (ENNReal.ofReal (8 : ℝ)) ^ s * (ENNReal.ofReal r') ^ s := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hs_nonneg]
      rw [h2]
      have h3 : (ENNReal.ofReal (8 : ℝ)) ^ s = ENNReal.ofReal ((8 : ℝ)^s) := by
        exact ENNReal.ofReal_rpow_of_nonneg (by norm_num) hs_nonneg
      rw [h3] <;> rfl
    have h11 : (262144 : ENNReal)^4 = ENNReal.ofReal ((262144 : ℝ)^4) := by norm_cast
    have h12 : ENNReal.ofReal C * ENNReal.ofReal ((8 : ℝ)^s) * ENNReal.ofReal ((262144 : ℝ)^4) =
        ENNReal.ofReal (C * (8 : ℝ)^s * (262144 : ℝ)^4) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)] <;> ring
    calc Ncover (δ / 4) E_int
      ≤ (262144 : ENNReal)^3 * Ncover (2 * δ) E_int := h_doubling
    _ ≤ (262144 : ENNReal)^3 * Ncover δ preimage := by
        exact mul_le_mul_left' h_forward _
    _ ≤ (262144 : ENNReal)^3 * Ncover δ (F ∩ Metric.closedBall y₀ (8 * r')) := by
        exact mul_le_mul_left' h_mono _
    _ ≤ (262144 : ENNReal)^3 * (ENNReal.ofReal C * (ENNReal.ofReal (8 * r')) ^ s * Ncover δ F) := by
        exact mul_le_mul_left' h_sset _
    _ ≤ (262144 : ENNReal)^3 * (ENNReal.ofReal C * (ENNReal.ofReal (8 * r')) ^ s * ((262144 : ENNReal) * Ncover (δ / 4) E')) := by
        set K_const := ENNReal.ofReal C * (ENNReal.ofReal (8 * r')) ^ s with hK_def
        have h5 : Ncover δ F ≤ (262144 : ENNReal) * Ncover (δ / 4) E' := h_backward
        have h6 : K_const * Ncover δ F ≤ K_const * ((262144 : ENNReal) * Ncover (δ / 4) E') :=
          mul_le_mul_left' h5 K_const
        have h7 : (262144 : ENNReal)^3 * (K_const * Ncover δ F) ≤
            (262144 : ENNReal)^3 * (K_const * ((262144 : ENNReal) * Ncover (δ / 4) E')) :=
          mul_le_mul_left' h6 _
        simpa [hK_def] using h7
    _ = (262144 : ENNReal)^4 * ENNReal.ofReal C * (ENNReal.ofReal (8 * r')) ^ s * Ncover (δ / 4) E' := by
        simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
    _ = ENNReal.ofReal (C * (8 : ℝ)^s * (262144 : ℝ)^4) * (ENNReal.ofReal r') ^ s * Ncover (δ / 4) E' := by
        have h14 : (262144 : ENNReal)^4 * ENNReal.ofReal C * ENNReal.ofReal ((8 : ℝ)^s) =
            ENNReal.ofReal (C * (8 : ℝ)^s * (262144 : ℝ)^4) := by
          rw [h11]
          have h_mul : ENNReal.ofReal ((262144 : ℝ)^4) * ENNReal.ofReal C * ENNReal.ofReal ((8 : ℝ)^s) =
              ENNReal.ofReal (((262144 : ℝ)^4) * C * ((8 : ℝ)^s)) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)] <;> rfl
          rw [h_mul]
          have h_real : ((262144 : ℝ)^4) * C * ((8 : ℝ)^s) = C * (8 : ℝ)^s * (262144 : ℝ)^4 := by ring
          rw [h_real]
        have h13 : (262144 : ENNReal)^4 * ENNReal.ofReal C * (ENNReal.ofReal (8 * r')) ^ s =
            ENNReal.ofReal (C * (8 : ℝ)^s * (262144 : ℝ)^4) * (ENNReal.ofReal r') ^ s := by
          rw [h9]
          have h_assoc : (262144 : ENNReal)^4 * ENNReal.ofReal C * (ENNReal.ofReal ((8 : ℝ)^s) * (ENNReal.ofReal r') ^ s) =
              ((262144 : ENNReal)^4 * ENNReal.ofReal C * ENNReal.ofReal ((8 : ℝ)^s)) * (ENNReal.ofReal r') ^ s := by
            simp [mul_assoc]
          rw [h_assoc, h14]
          <;> rfl
        rw [h13] <;> simp [mul_assoc]
  · have h_empty' : E_int = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using h_empty
    have h_goal : Ncover (δ / 4) E_int ≤
        ENNReal.ofReal (C * (8 : ℝ)^s * (262144 : ℝ)^4) * (ENNReal.ofReal r') ^ s * Ncover (δ / 4) E' := by
      rw [h_empty']
      simp [Ncover, Metric.externalCoveringNumber_empty] <;> positivity
    exact h_goal

/-- Square-root regularity transfer under S0. -/
lemma S0_squareRootRegular {δ t C K : ℝ} {P : Set Plane}
    (h : IsSquareRootRegular δ t C K P) :
    IsSquareRootRegular (δ / 4) t (C * (4 : ℝ)^t) (K * (4 : ℝ)^t) (S0 '' P) := by
  have h1 : IsDeltaSSet (δ / 4) t (C * (4 : ℝ)^t) (S0 '' P) := S0_sset h.1
  have hδ_pos : 0 < δ := h.1.2.1
  have h_main1 : Ncover (Real.sqrt (δ / 4)) (S0 '' P) ≤ Ncover (Real.sqrt δ) P := by
    have h_sqrt : Real.sqrt (δ / 4) = Real.sqrt δ / 2 := by
      have h : Real.sqrt (δ / 4) = Real.sqrt δ / Real.sqrt 4 := Real.sqrt_div hδ_pos.le 4
      rw [h]
      have h2 : Real.sqrt 4 = 2 := by
        rw [Real.sqrt_eq_cases] <;> norm_num
      rw [h2] <;> ring
    rw [h_sqrt]
    have h_le : Real.sqrt δ / 4 ≤ Real.sqrt δ / 2 := by linarith [Real.sqrt_nonneg δ]
    have h_le_nn : (Real.sqrt δ / 4).toNNReal ≤ (Real.sqrt δ / 2).toNNReal := by
      have h_nonneg1 : 0 ≤ Real.sqrt δ / 4 := by positivity
      have h_nonneg2 : 0 ≤ Real.sqrt δ / 2 := by positivity
      rw [Real.toNNReal_of_nonneg h_nonneg1, Real.toNNReal_of_nonneg h_nonneg2]
      exact h_le
    have h_anti : Ncover (Real.sqrt δ / 2) (S0 '' P) ≤ Ncover (Real.sqrt δ / 4) (S0 '' P) := by
      exact_mod_cast Metric.externalCoveringNumber_anti (A := S0 '' P) h_le_nn
    have h_eq : Ncover (Real.sqrt δ / 4) (S0 '' P) = Ncover (Real.sqrt δ) P := by
      have h4 : Real.sqrt δ / 4 = (Real.sqrt δ) / 4 := by ring
      rw [h4]
      exact S0_ncover (by positivity)
    exact le_trans h_anti (le_of_eq h_eq)
  have h_main2 : Ncover (Real.sqrt δ) P ≤ ENNReal.ofReal (K * Real.rpow δ (-t / 2)) := h.2
  have h_t_nonneg : 0 ≤ t := h.1.2.2.2.1
  have hK_nonneg : 0 ≤ K := by
    by_contra hK_neg
    have hK_lt : K < 0 := by linarith
    have h_rpow_pos : 0 < Real.rpow δ (-t / 2) := Real.rpow_pos_of_pos hδ_pos _
    have h_prod_neg : K * Real.rpow δ (-t / 2) < 0 := by
      exact mul_neg_of_neg_of_pos hK_lt h_rpow_pos
    have h_ofReal_zero : ENNReal.ofReal (K * Real.rpow δ (-t / 2)) = 0 := by
      rw [ENNReal.ofReal_eq_zero.mpr] <;> linarith
    have h2 : Ncover (Real.sqrt δ) P ≤ ENNReal.ofReal (K * Real.rpow δ (-t / 2)) := h.2
    rw [h_ofReal_zero] at h2
    have hP_nonempty : P.Nonempty := h.1.1
    have hNcover_pos : (0 : ENNReal) < Ncover (Real.sqrt δ) P := by
      have hP : P.Nonempty := hP_nonempty
      have h_pos_nat : (0 : ℕ∞) < Metric.externalCoveringNumber (Real.sqrt δ).toNNReal P :=
        Metric.externalCoveringNumber_pos_iff.mpr hP
      have h_ne_nat : Metric.externalCoveringNumber (Real.sqrt δ).toNNReal P ≠ 0 := ne_of_gt h_pos_nat
      have h_ne_enn : Ncover (Real.sqrt δ) P ≠ 0 := by
        intro h
        have h' : (Metric.externalCoveringNumber (Real.sqrt δ).toNNReal P : ENNReal) = 0 := by
          simpa [Ncover] using h
        have h'' : Metric.externalCoveringNumber (Real.sqrt δ).toNNReal P = 0 := by
          exact_mod_cast h'
        exact h_ne_nat h''
      exact pos_iff_ne_zero.mpr h_ne_enn
    exact not_le.mpr hNcover_pos h2
  have h6 : Real.rpow (δ / 4) (-t / 2) = (4 : ℝ)^(t / 2) * Real.rpow δ (-t / 2) := by
    have h_pos1 : 0 ≤ δ := hδ_pos.le
    have h_pos2 : (0 : ℝ) ≤ 1 / 4 := by norm_num
    have h_eq1 : Real.rpow (δ / 4) (-t / 2) =
        Real.rpow δ (-t / 2) * Real.rpow (1 / 4 : ℝ) (-t / 2) := by
      have h : δ / 4 = δ * (1 / 4 : ℝ) := by ring
      rw [h]
      exact Real.mul_rpow h_pos1 h_pos2
    rw [h_eq1]
    have h_pos3 : (0 : ℝ) < 1 / 4 := by norm_num
    have h_pos4 : (0 : ℝ) < 4 := by norm_num
    have h8 : Real.rpow (1 / 4 : ℝ) (-t / 2) = Real.rpow (4 : ℝ) (t / 2) := by
      have hpos : 0 ≤ (1 / 4 : ℝ) := by norm_num
      have h_exp : (-t / 2) = -(t / 2) := by ring
      have h1 : Real.rpow (1 / 4 : ℝ) (-t / 2) = (Real.rpow (1 / 4 : ℝ) (t / 2))⁻¹ := by
        rw [h_exp]
        exact Real.rpow_neg hpos (t / 2)
      have h2 : Real.rpow (1 / 4 : ℝ) (t / 2) * Real.rpow (4 : ℝ) (t / 2) = 1 := by
        have h3 : Real.rpow ((1 / 4 : ℝ) * (4 : ℝ)) (t / 2) =
            Real.rpow (1 / 4 : ℝ) (t / 2) * Real.rpow (4 : ℝ) (t / 2) :=
          Real.mul_rpow (by norm_num) (by norm_num)
        have h4 : (1 / 4 : ℝ) * (4 : ℝ) = 1 := by norm_num
        rw [←h3, h4]
        simp
      have h5 : (Real.rpow (1 / 4 : ℝ) (t / 2))⁻¹ = Real.rpow (4 : ℝ) (t / 2) :=
        inv_eq_of_mul_eq_one_right h2
      rw [h1, h5]
    rw [h8]
    have h9 : (4 : ℝ)^(t / 2) = Real.rpow (4 : ℝ) (t / 2) := by simp
    rw [h9] <;> ring
  have h5 : K * Real.rpow δ (-t / 2) ≤
      (K * (4 : ℝ)^t) * Real.rpow (δ / 4) (-t / 2) := by
    rw [h6]
    have h7 : 1 ≤ (4 : ℝ)^t := by
      apply Real.one_le_rpow <;> norm_num <;> linarith
    have h8 : 1 ≤ (4 : ℝ)^(t / 2) := by
      apply Real.one_le_rpow <;> norm_num <;> linarith
    have h9 : 0 ≤ Real.rpow δ (-t / 2) := Real.rpow_nonneg hδ_pos.le _
    have h10 : 1 ≤ (4 : ℝ)^t * (4 : ℝ)^(t / 2) := by
      calc 1
        = 1 * 1 := by ring
      _ ≤ (4 : ℝ)^t * (4 : ℝ)^(t / 2) := by gcongr
    calc K * Real.rpow δ (-t / 2)
      = 1 * (K * Real.rpow δ (-t / 2)) := by ring
    _ ≤ ((4 : ℝ)^t * (4 : ℝ)^(t / 2)) * (K * Real.rpow δ (-t / 2)) := by gcongr
    _ = (K * (4 : ℝ)^t) * ((4 : ℝ)^(t / 2) * Real.rpow δ (-t / 2)) := by ring
  exact ⟨h1, le_trans h_main1 (le_trans h_main2 (ENNReal.ofReal_le_ofReal h5))⟩

end DirecretisedFurstenbergEstimate.RegularIncidence

end
