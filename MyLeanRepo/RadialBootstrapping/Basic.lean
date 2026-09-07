module

/-
  RadialBootstrapping/Basic.lean

  Canonical definitions for the radial bootstrapping of measure thin tubes.
  ALL modules in this development must import this file and use these
  definitions to ensure consistency.

  Main contents:
  1. `Point` — type alias for Euclidean plane
  2. `Line2` — subtype of affine subspaces that are lines (finrank 1)
  3. `tube` — metric thickening of a line
  4. `IsDeltaSet` — (δ, s, C)-set condition using covering numbers
  5. `IsConcentrated` — concentration of measure in a tube
  6. Common imports and notation

  Whiteprint node: basic-definitions
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set Finset
open scoped Classical

noncomputable section

namespace RadialBootstrapping

-- ============================================================================
-- 1. Point and Line types
-- ============================================================================

/-- The Euclidean plane R². -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- Inner product (dot product) of two Points. -/
abbrev dot (a b : Point) : ℝ := inner ℝ a b

/-- A line in R²: an affine subspace whose direction has real finrank 1. -/
def Line2 : Type :=
  {ℓ : AffineSubspace ℝ Point // Module.finrank ℝ ℓ.direction = 1}

/-- Classical decidable equality for Line2. -/
instance : DecidableEq Line2 :=
  fun a b => Classical.dec (a = b)

/-- The underlying affine subspace of a line. -/
def Line2.toAffine (L : Line2) : AffineSubspace ℝ Point := L.val

/-- The underlying set of a line. -/
def Line2.toSet (L : Line2) : Set Point := (L.val : Set Point)

/-- A line contains a point iff the point is in the underlying affine subspace. -/
lemma Line2.mem_iff (L : Line2) (x : Point) : x ∈ L.toSet ↔ x ∈ L.val := Iff.rfl

-- ============================================================================
-- 2. Tubes
-- ============================================================================

/-- The open r-tube around a line is its metric r-thickening.
This matches `N_r(ℓ)` in the paper and `Metric.thickening` in Mathlib. -/
def tube (r : ℝ) (L : Line2) : Set Point :=
  Metric.thickening r L.toSet

lemma tube_mono {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) (L : Line2) :
    tube r₁ L ⊆ tube r₂ L :=
  Metric.thickening_mono h L.toSet

lemma line_subset_tube {r : ℝ} (hr : 0 < r) (L : Line2) :
    L.toSet ⊆ tube r L := by
  intro x hx
  simp only [tube, Metric.mem_thickening_iff]
  exact ⟨x, hx, by simpa using hr⟩

lemma tube_isOpen (r : ℝ) (L : Line2) : IsOpen (tube r L) :=
  Metric.isOpen_thickening

lemma tube_measurableSet (r : ℝ) (L : Line2) : MeasurableSet (tube r L) :=
  (tube_isOpen r L).measurableSet

-- ============================================================================
-- 2b. Metric on Line2
-- ============================================================================

/-- Orthogonal projection onto a submodule, viewed as a map Point → Point. -/
def submoduleProj (V : Submodule ℝ Point) : Point →L[ℝ] Point :=
  V.subtypeₗᵢ.toContinuousLinearMap.comp V.orthogonalProjectionOnto

/-- `submoduleProj V` equals `V.starProjection`, the standard orthogonal projection. -/
lemma submoduleProj_eq_starProjection (V : Submodule ℝ Point) :
    submoduleProj V = V.starProjection := by
  ext x
  have h1 : submoduleProj V x = (V.orthogonalProjectionOnto x : Point) := by
    rfl
  have h2 : V.starProjection x = (V.orthogonalProjectionOnto x : Point) :=
    Submodule.starProjection_apply V x
  rw [h1, h2]

/-- Distance between two subspaces: operator norm of the difference of their
orthogonal projections. Standard metric on the Grassmannian. -/
def submoduleDirDist (V W : Submodule ℝ Point) : ℝ :=
  ‖submoduleProj V - submoduleProj W‖

lemma submoduleDirDist_self (V : Submodule ℝ Point) : submoduleDirDist V V = 0 := by
  have h : submoduleProj V - submoduleProj V = (0 : Point →L[ℝ] Point) := by
    ext x; simp
  rw [submoduleDirDist, h]; simp

lemma submoduleDirDist_comm (V W : Submodule ℝ Point) :
    submoduleDirDist V W = submoduleDirDist W V := by
  have h2 : submoduleProj V - submoduleProj W = -(submoduleProj W - submoduleProj V) := by
    ext x; simp <;> abel
  calc submoduleDirDist V W = ‖submoduleProj V - submoduleProj W‖ := by rfl
    _ = ‖-(submoduleProj W - submoduleProj V)‖ := by rw [h2]
    _ = ‖submoduleProj W - submoduleProj V‖ := by rw [norm_neg]
    _ = submoduleDirDist W V := by rfl

lemma submoduleDirDist_triangle (V W U : Submodule ℝ Point) :
    submoduleDirDist V U ≤ submoduleDirDist V W + submoduleDirDist W U := by
  have h : submoduleProj V - submoduleProj U =
      (submoduleProj V - submoduleProj W) + (submoduleProj W - submoduleProj U) := by
    ext x; simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply] <;> abel_nf
  calc submoduleDirDist V U = ‖submoduleProj V - submoduleProj U‖ := by rfl
    _ = ‖(submoduleProj V - submoduleProj W) + (submoduleProj W - submoduleProj U)‖ := by rw [h]
    _ ≤ ‖submoduleProj V - submoduleProj W‖ + ‖submoduleProj W - submoduleProj U‖ := norm_add_le _ _
    _ = submoduleDirDist V W + submoduleDirDist W U := by rfl

lemma submoduleDirDist_eq_zero {V W : Submodule ℝ Point} :
    submoduleDirDist V W = 0 ↔ V = W := by
  constructor
  · intro h
    have hP : submoduleProj V = submoduleProj W := by
      have h' : ‖submoduleProj V - submoduleProj W‖ = 0 := h
      have h'' : submoduleProj V - submoduleProj W = 0 := by simpa [norm_eq_zero] using h'
      exact sub_eq_zero.mp h''
    have h1 : V ≤ W := by
      intro v hv
      have h_goal : V.orthogonalProjectionOnto v = (⟨v, hv⟩ : V) :=
        Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨v, hv⟩ : V)
      have h2 : submoduleProj V v = v := by
        dsimp only [submoduleProj]
        have h3 : (V.subtypeₗᵢ.toContinuousLinearMap) (V.orthogonalProjectionOnto v) = v := by
          rw [h_goal] <;> rfl
        exact h3
      rw [hP] at h2
      have h4 : submoduleProj W v = v := h2
      have h5 : ↑(W.orthogonalProjectionOnto v) = v := h4
      have h6 : ↑(W.orthogonalProjectionOnto v) ∈ W := (W.orthogonalProjectionOnto v).property
      rw [h5] at h6; exact h6
    have h2 : W ≤ V := by
      intro w hw
      have h_goal : W.orthogonalProjectionOnto w = (⟨w, hw⟩ : W) :=
        Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨w, hw⟩ : W)
      have h3 : submoduleProj W w = w := by
        dsimp only [submoduleProj]
        have h4 : (W.subtypeₗᵢ.toContinuousLinearMap) (W.orthogonalProjectionOnto w) = w := by
          rw [h_goal] <;> rfl
        exact h4
      rw [←hP] at h3
      have h5 : submoduleProj V w = w := h3
      have h6 : ↑(V.orthogonalProjectionOnto w) = w := h5
      have h7 : ↑(V.orthogonalProjectionOnto w) ∈ V := (V.orthogonalProjectionOnto w).property
      rw [h6] at h7; exact h7
    exact le_antisymm h1 h2
  · rintro rfl; exact submoduleDirDist_self V

/-- A line with finrank 1 direction is nonempty. -/
lemma Line2.exists_point (L : Line2) : ∃ (x : Point), x ∈ L.toAffine := by
  rcases L with ⟨ℓ, hfin⟩
  have hV : ℓ.direction ≠ (⊥ : Submodule ℝ Point) := by
    intro hbot
    rw [hbot] at hfin
    simp at hfin <;> norm_num at hfin
  by_cases hne : (ℓ : Set Point).Nonempty
  · exact hne
  · have h_empty : (ℓ : Set Point) = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have h_bot : ℓ = (⊥ : AffineSubspace ℝ Point) := by
      exact (AffineSubspace.coe_eq_bot_iff ℓ).mp h_empty
    have h_dir_bot : ℓ.direction = (⊥ : Submodule ℝ Point) := by
      rw [h_bot, AffineSubspace.direction_bot]
    have h_false : False := hV h_dir_bot
    exact h_false.elim

/-- The point on a line closest to the origin, computed as `p - proj_V(p)`
for any p ∈ L, where V is the direction subspace. -/
def Line2.closestPoint (L : Line2) : Point :=
  let V := L.toAffine.direction
  let p : Point := Classical.choose L.exists_point
  p - V.orthogonalProjectionFn p

lemma Line2.closestPoint_mem (L : Line2) :
    Line2.closestPoint L ∈ L.toAffine := by
  rcases L with ⟨ℓ, hfin⟩
  dsimp only [Line2.closestPoint]
  let V := ℓ.direction
  let p : Point := Classical.choose (Line2.exists_point ⟨ℓ, hfin⟩)
  have hp : p ∈ ℓ := Classical.choose_spec (Line2.exists_point ⟨ℓ, hfin⟩)
  have h1 : V.orthogonalProjectionFn p ∈ V := by
    have h2 : V.orthogonalProjectionFn p = ↑(V.orthogonalProjectionOnto p) := by rfl
    rw [h2]; exact (V.orthogonalProjectionOnto p).property
  have h2 : -V.orthogonalProjectionFn p ∈ V := V.neg_mem h1
  have h3 : (-V.orthogonalProjectionFn p) +ᵥ p ∈ ℓ :=
    ℓ.vadd_mem_of_mem_direction h2 hp
  have h4 : (-V.orthogonalProjectionFn p) +ᵥ p = p - V.orthogonalProjectionFn p := by
    have h5 : (-V.orthogonalProjectionFn p) +ᵥ p = (-V.orthogonalProjectionFn p) + p := by
      exact PiLp.ext (congrFun rfl)
    rw [h5]
    have h6 : (-V.orthogonalProjectionFn p) + p = p - V.orthogonalProjectionFn p := by
      abel
    exact h6
  rw [h4] at h3
  exact h3

/-- Every Line2's affine subspace is nonempty. -/
instance (L : Line2) : Nonempty L.toAffine :=
  ⟨⟨L.closestPoint, L.closestPoint_mem⟩⟩

/-- `closestPoint L` equals the Euclidean orthogonal projection of the origin
onto the affine subspace, i.e. `EuclideanGeometry.orthogonalProjection L.toAffine 0`. -/
lemma Line2.closestPoint_eq_orthogonalProjection (L : Line2) :
    L.closestPoint = EuclideanGeometry.orthogonalProjection L.toAffine 0 := by
  let V := L.toAffine.direction
  let p : Point := Classical.choose L.exists_point
  have hp : p ∈ L.toAffine := Classical.choose_spec L.exists_point
  letI : Nonempty L.toAffine := ⟨⟨p, hp⟩⟩
  have h : (EuclideanGeometry.orthogonalProjection L.toAffine 0 : Point) =
      (V.orthogonalProjectionOnto ((0 : Point) -ᵥ p) : Point) +ᵥ p :=
    EuclideanGeometry.orthogonalProjection_apply_mem (s := L.toAffine) (x := p) (hx := hp)
  have h5 : (0 : Point) -ᵥ p = -p := by simp [vsub_eq_sub]
  have h_main : (EuclideanGeometry.orthogonalProjection L.toAffine 0 : Point) =
      p - V.orthogonalProjectionFn p := by
    rw [h, h5]
    have h_neg : (V.orthogonalProjectionOnto (-p) : Point) = -V.orthogonalProjectionFn p := by
      have h1 : (V.orthogonalProjectionOnto (-p) : Point) = -(V.orthogonalProjectionOnto p : Point) := by
        exact_mod_cast ContinuousLinearMap.map_neg V.orthogonalProjectionOnto p
      have h2 : (V.orthogonalProjectionOnto p : Point) = V.orthogonalProjectionFn p :=
        (Submodule.orthogonalProjectionFn_eq p).symm
      rw [h1, h2] <;> rfl
    rw [h_neg]
    have h_vadd : (-V.orthogonalProjectionFn p) +ᵥ p = p - V.orthogonalProjectionFn p := by
      have h3 : (-V.orthogonalProjectionFn p) +ᵥ p = (-V.orthogonalProjectionFn p) + p := by exact PiLp.ext (congrFun rfl)
      rw [h3] <;> abel
    exact h_vadd
  exact h_main.symm

/-- Direction distance between two lines. -/
def lineDirDist (L₁ L₂ : Line2) : ℝ :=
  submoduleDirDist L₁.toAffine.direction L₂.toAffine.direction

/-- Offset distance between two lines: distance between their closest
points to the origin. -/
def lineOffsetDist (L₁ L₂ : Line2) : ℝ :=
  dist (Line2.closestPoint L₁) (Line2.closestPoint L₂)

/-- Distance on Line2: sum of direction and offset distances.
This matches the metric on `DirecretisedFurstenbergEstimate.AffineLine`, making
the canonical coercion an isometry. -/
def lineDist (L₁ L₂ : Line2) : ℝ :=
  lineDirDist L₁ L₂ + lineOffsetDist L₁ L₂

lemma lineDist_self (L : Line2) : lineDist L L = 0 := by
  rw [lineDist]
  have h1 : lineDirDist L L = 0 := submoduleDirDist_self _
  have h2 : lineOffsetDist L L = 0 := dist_self _
  rw [h1, h2] <;> ring

lemma lineDist_comm (L₁ L₂ : Line2) : lineDist L₁ L₂ = lineDist L₂ L₁ := by
  rw [lineDist, lineDist]
  have h1 : lineDirDist L₁ L₂ = lineDirDist L₂ L₁ := submoduleDirDist_comm _ _
  have h2 : lineOffsetDist L₁ L₂ = lineOffsetDist L₂ L₁ := dist_comm _ _
  rw [h1, h2] <;> abel

lemma lineDist_eq_zero {L₁ L₂ : Line2} : lineDist L₁ L₂ = 0 ↔ L₁ = L₂ := by
  constructor
  · intro h
    have hsum : lineDirDist L₁ L₂ + lineOffsetDist L₁ L₂ = 0 := by
      simpa [lineDist] using h
    have hpos1 : 0 ≤ lineDirDist L₁ L₂ := by
      unfold lineDirDist submoduleDirDist; positivity
    have hpos2 : 0 ≤ lineOffsetDist L₁ L₂ := by
      unfold lineOffsetDist; exact dist_nonneg
    have hd : lineDirDist L₁ L₂ = 0 := by linarith
    have ho : lineOffsetDist L₁ L₂ = 0 := by linarith
    have hdir : L₁.toAffine.direction = L₂.toAffine.direction :=
      submoduleDirDist_eq_zero.mp hd
    have hp : Line2.closestPoint L₁ = Line2.closestPoint L₂ := by
      simpa [lineOffsetDist, dist_eq_zero] using ho
    have h_main : L₁.toAffine = L₂.toAffine := by
      have hp1 : Line2.closestPoint L₁ ∈ L₁.toAffine :=
        Line2.closestPoint_mem L₁
      have hp2 : Line2.closestPoint L₁ ∈ L₂.toAffine := by
        rw [hp] <;> exact Line2.closestPoint_mem L₂
      exact (AffineSubspace.eq_iff_direction_eq_of_mem hp1 hp2).mpr hdir
    apply Subtype.ext
    exact h_main
  · rintro rfl
    exact lineDist_self L₁

lemma lineDist_triangle (L₁ L₂ L₃ : Line2) :
    lineDist L₁ L₃ ≤ lineDist L₁ L₂ + lineDist L₂ L₃ := by
  have h1 : lineDirDist L₁ L₃ ≤ lineDirDist L₁ L₂ + lineDirDist L₂ L₃ :=
    submoduleDirDist_triangle _ _ _
  have h2 : lineOffsetDist L₁ L₃ ≤ lineOffsetDist L₁ L₂ + lineOffsetDist L₂ L₃ :=
    dist_triangle _ _ _
  dsimp only [lineDist]
  linarith

/-- Metric space instance on Line2. -/
instance : MetricSpace Line2 where
  dist := lineDist
  dist_self := lineDist_self
  eq_of_dist_eq_zero {x y} h := lineDist_eq_zero.mp h
  dist_comm := lineDist_comm
  dist_triangle := lineDist_triangle

-- ============================================================================
-- 3. (δ, s, C)-sets
-- ============================================================================

/-- A set `P` in a metric space is a `(δ, s, C)`-set if for every center `x`
and radius `r ≥ δ`, the external `δ`-covering number of `P ∩ ball x r` is at
most `C * r^s` times the external `δ`-covering number of `P`.

We use external covering numbers because they are monotone under set inclusion,
which is needed for the restriction property (large subsets inherit the property
with a worsened constant).

This is the discretized analogue of a Frostman condition, used throughout
the OSW bootstrapping argument.

Parameters:
- `δ > 0`: discretization scale
- `s ≥ 0`: dimension exponent
- `C ≥ 0`: constant
- `P`: the set
-/
def IsDeltaSet {X : Type*} [PseudoMetricSpace X]
    (δ s C : ℝ) (hδ : 0 < δ) (hs : 0 ≤ s) (hC : 0 ≤ C)
    (P : Set X) : Prop :=
  ∀ (x : X) (r : ℝ) (hr : δ ≤ r),
    (Metric.externalCoveringNumber ⟨δ, hδ.le⟩ (P ∩ ball x r) : ENNReal) ≤
      ENNReal.ofReal (C * Real.rpow r s) *
        (Metric.externalCoveringNumber ⟨δ, hδ.le⟩ P : ENNReal)

namespace IsDeltaSet

variable {X : Type*} [PseudoMetricSpace X] {δ s C : ℝ}
  {hδ : 0 < δ} {hs : 0 ≤ s} {hC : 0 ≤ C} {P : Set X}

lemma spec (h : IsDeltaSet δ s C hδ hs hC P) :
    ∀ (x : X) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber ⟨δ, hδ.le⟩ (P ∩ ball x r) : ENNReal) ≤
        ENNReal.ofReal (C * Real.rpow r s) *
          (Metric.externalCoveringNumber ⟨δ, hδ.le⟩ P : ENNReal) := h

/-- If `P` is a `(δ, s, C)`-set and `C ≤ C'`, then `P` is a `(δ, s, C')`-set. -/
lemma mono_C (h : IsDeltaSet δ s C hδ hs hC P) {C' : ℝ} (hC' : 0 ≤ C')
    (hCC' : C ≤ C') :
    IsDeltaSet δ s C' hδ hs hC' P := by
  intro x r hr
  have h₁ : 0 ≤ Real.rpow r s := Real.rpow_nonneg (by linarith) s
  have h₂ : C * Real.rpow r s ≤ C' * Real.rpow r s :=
    mul_le_mul_of_nonneg_right hCC' h₁
  have h₃ : ENNReal.ofReal (C * Real.rpow r s) ≤ ENNReal.ofReal (C' * Real.rpow r s) :=
    ENNReal.ofReal_le_ofReal h₂
  calc (Metric.externalCoveringNumber ⟨δ, hδ.le⟩ (P ∩ ball x r) : ENNReal)
    ≤ ENNReal.ofReal (C * Real.rpow r s) *
        (Metric.externalCoveringNumber ⟨δ, hδ.le⟩ P : ENNReal) := h.spec x r hr
  _ ≤ ENNReal.ofReal (C' * Real.rpow r s) *
        (Metric.externalCoveringNumber ⟨δ, hδ.le⟩ P : ENNReal) := by gcongr

/-- Restriction property: if `P` is a `(δ, s, C)`-set and `Q ⊆ P` has
external covering number at least `1/K` times that of `P`, then `Q` is a
`(δ, s, C*K)`-set. This corresponds to OSW Remark 2.2: a large subset of a
`(δ,s,C)`-set is a `(δ,s,C/K)`-set (with our parameterization). -/
lemma restrict (h : IsDeltaSet δ s C hδ hs hC P) {Q : Set X} {K : ℝ}
    (hK : 0 ≤ K) (hQ : Q ⊆ P)
    (hden : (Metric.externalCoveringNumber ⟨δ, hδ.le⟩ P : ENNReal) ≤
      ENNReal.ofReal K * (Metric.externalCoveringNumber ⟨δ, hδ.le⟩ Q : ENNReal)) :
    IsDeltaSet δ s (C * K) hδ hs (mul_nonneg hC hK) Q := by
  intro x r hr
  let δn : NNReal := ⟨δ, hδ.le⟩
  have h_sub : Q ∩ ball x r ⊆ P ∩ ball x r := by gcongr <;> tauto
  have h1 : (Metric.externalCoveringNumber δn (Q ∩ ball x r) : ENNReal) ≤
      (Metric.externalCoveringNumber δn (P ∩ ball x r) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set h_sub
  have h2 : C * K * Real.rpow r s = C * Real.rpow r s * K := by ring
  calc
    (Metric.externalCoveringNumber δn (Q ∩ ball x r) : ENNReal)
      ≤ (Metric.externalCoveringNumber δn (P ∩ ball x r) : ENNReal) := h1
    _ ≤ ENNReal.ofReal (C * Real.rpow r s) *
          (Metric.externalCoveringNumber δn P : ENNReal) := h.spec x r hr
    _ ≤ ENNReal.ofReal (C * Real.rpow r s) *
          (ENNReal.ofReal K * (Metric.externalCoveringNumber δn Q : ENNReal)) := by gcongr
    _ = ENNReal.ofReal (C * K * Real.rpow r s) *
          (Metric.externalCoveringNumber δn Q : ENNReal) := by
      have h_nonneg1 : 0 ≤ C * Real.rpow r s := by
        exact mul_nonneg hC (Real.rpow_nonneg (by linarith) s)
      have h_nonneg2 : 0 ≤ K := hK
      have h_mul : ENNReal.ofReal (C * Real.rpow r s) * ENNReal.ofReal K =
          ENNReal.ofReal (C * Real.rpow r s * K) := by
        exact Eq.symm (ENNReal.ofReal_mul h_nonneg1)
      have h_main : ENNReal.ofReal (C * Real.rpow r s) *
            (ENNReal.ofReal K * (Metric.externalCoveringNumber δn Q : ENNReal)) =
          ENNReal.ofReal (C * K * Real.rpow r s) *
            (Metric.externalCoveringNumber δn Q : ENNReal) := by
        have h3 : C * Real.rpow r s * K = C * K * Real.rpow r s := by ring
        rw [← mul_assoc, h_mul]
        rw [show ENNReal.ofReal (C * Real.rpow r s * K) = ENNReal.ofReal (C * K * Real.rpow r s)
          from by rw [h3]]
      exact h_main

end IsDeltaSet

-- ============================================================================
-- 4. Concentration of measure in tubes
-- ============================================================================

/-- A tube `T` is *concentrated* on `Y_x` w.r.t. measure `ν` at scale `r^κ`
if there exists a ball of radius `r^κ` containing at least 1/3 of the mass
`ν(T ∩ Y_x)`.

This is the definition used in the concentrated/non-concentrated case split
of the OSW bootstrapping argument.

Parameters:
- `ν`: measure (values in ENNReal)
- `Y_x`: the fiber subset
- `T`: the tube carrier set
- `r`: tube width
- `κ`: concentration exponent (typically `14τ/(1-σ)`)
-/
def IsConcentrated {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (ν : Measure X) (Y_x T : Set X) (r κ : ℝ) : Prop :=
  ∃ (center : X),
    ν (T ∩ ball center (Real.rpow r κ) ∩ Y_x) ≥
      (1 / 3 : ENNReal) * ν (T ∩ Y_x)

/-- A tube is *non-concentrated* if no ball of radius `r^κ` contains more
than 1/3 of its mass. -/
def IsNonConcentrated {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (ν : Measure X) (Y_x T : Set X) (r κ : ℝ) : Prop :=
  ∀ (center : X),
    ν (T ∩ ball center (Real.rpow r κ) ∩ Y_x) ≤
      (1 / 3 : ENNReal) * ν (T ∩ Y_x)

lemma not_concentrated_imp_nonconcentrated {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    {ν : Measure X} {Y_x T : Set X} {r κ : ℝ} :
    ¬ IsConcentrated ν Y_x T r κ → IsNonConcentrated ν Y_x T r κ := by
  intro h
  intro center
  have h' : ¬ (ν (T ∩ ball center (Real.rpow r κ) ∩ Y_x) ≥ (1 / 3 : ENNReal) * ν (T ∩ Y_x)) := by
    intro hge
    exact h ⟨center, hge⟩
  exact le_of_not_ge h'

-- ============================================================================
-- 5. Measure convention helpers
-- ============================================================================

/-- Convert a `ProbabilityMeasure` to a `Measure` for ENNReal arithmetic.
This is the standard coercion. -/
abbrev PMtoMeasure {α : Type*} [MeasurableSpace α]
    (ν : ProbabilityMeasure α) : Measure α := ↑ν

/-- Bridge from `NNReal` thin-tubes bound to `ENNReal`.
The target theorem uses `ν₂ S ≤ Real.toNNReal (K * r ^ β)`.
For internal proofs using `ENNReal`, this converts the bound. -/
lemma thinTubesBound_toENNReal {K r β : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (hβ : 0 ≤ β) :
    ENNReal.ofReal (K * r ^ β) = ↑(Real.toNNReal (K * r ^ β)) := by
  have hpos : 0 ≤ K * r ^ β := by
    have h1 : 0 ≤ r ^ β := Real.rpow_nonneg hr β
    positivity
  have h_eq : (↑(Real.toNNReal (K * r ^ β)) : ENNReal) = ENNReal.ofReal (K * r ^ β) := by
    exact ENNReal.ofNNReal_toNNReal (K * r ^ β)
  exact h_eq.symm

-- ============================================================================
-- 6. Bounded overlap structure for tube families
-- ============================================================================

local instance : DecidableEq Line2 := Classical.decEq _

/-- Properties of a maximal r-separated family of 2r-tubes T^r.
The constants c, C₁, C₂, C₃ are parameters to the structure.

Properties:
(i)   Cardinality |T^r| ≤ C₁ * r^{-2}
(ii)  Covering: every r-tube ∩ B² is covered by at most C₂ tubes from T (widened to 2r)
(iii) Separation: distinct lines in T are at least c·r apart in lineDist
(iv)  Bounded overlap: number of tubes containing both x and y is ≤ C₃ / dist(x,y)
-/

structure MaximalTubeFamily (c C₁ C₂ C₃ r : ℝ) (T : Finset Line2) : Prop where
  r_pos : 0 < r
  c_pos : 0 < c
  C₁_pos : 0 < C₁
  C₂_pos : 0 < C₂
  C₃_pos : 0 < C₃
  -- (i) Cardinality ~ r^{-2}
  card_le : (T.card : ℝ) ≤ C₁ * (1 / r ^ 2)
  -- (ii) Covering: every r-tube intersecting the unit ball is covered by
  -- at most C₂ tubes from T (each widened to 2r)
  covering : ∀ (L : Line2),
    ∃ (S : Finset Line2), S ⊆ T ∧ S.card ≤ Nat.ceil C₂ ∧
      (tube r L ∩ ball (0 : Point) 1) ⊆ ⋃ L' ∈ S, tube (2 * r) L'
  -- (iii) Separation: distinct lines in T are at least c·r apart in lineDist
  separation : ∀ L₁ ∈ T, ∀ L₂ ∈ T, L₁ ≠ L₂ → c * r ≤ lineDist L₁ L₂
  -- (iv) Bounded overlap: at most C₃ / dist(x,y) tubes contain both x and y
  bounded_overlap : ∀ (x y : Point), x ≠ y →
    (T.filter (fun L => x ∈ tube (2 * r) L ∧ y ∈ tube (2 * r) L)).card ≤
      Nat.ceil (C₃ / dist x y)

-- We fix universal constants c, C₁, C₂, C₃ for tube family constructions.
-- (These are existentially quantified in the existence theorem.)

end RadialBootstrapping
