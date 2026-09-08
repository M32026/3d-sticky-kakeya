/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Homotopy.Contractible

@[expose] public section

/-!
# Homology of Punctured Euclidean Space

We prove that ℝ^m \ {0} deformation retracts onto the unit sphere S^{m-1},
and therefore has isomorphic singular homology groups.

## Main results

- `puncturedToSphere` / `sphereToPunctured`: the retraction and inclusion maps
- `continuous_puncturedToSphere` / `continuous_sphereToPunctured`: continuity proofs
-/

noncomputable section

open Metric ContinuousMap

universe w v u

namespace Topology.EuclideanSpace

variable {m : ℕ} [Nonempty (Fin m)]

/-- The punctured Euclidean space ℝ^m \ {0}. -/
abbrev PuncturedSpace (m : ℕ) [Nonempty (Fin m)] : Type _ :=
  {x : EuclideanSpace ℝ (Fin m) // x ≠ 0}

/-- The unit sphere S^{m-1} in ℝ^m. -/
abbrev UnitSphere (m : ℕ) [Nonempty (Fin m)] : Type _ :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1

section Maps

/-- The retraction map r : ℝ^m \ {0} → S^{m-1} given by r(x) = x/‖x‖. -/
def puncturedToSphere (x : PuncturedSpace m) : UnitSphere m :=
  ⟨(1 / ‖x.val‖) • x.val, by
    have h₁ : 0 < ‖x.val‖ := norm_pos_iff.mpr x.property
    have h₂ : ‖(1 / ‖x.val‖) • x.val‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (show 0 ≤ 1 / ‖x.val‖ from by positivity)]
      ; field_simp [h₁.ne']
    have h₃ : dist ((1 / ‖x.val‖) • x.val) (0 : EuclideanSpace ℝ (Fin m)) = 1 := by
      simpa [dist_zero_right] using h₂
    exact h₃⟩

/-- The inclusion map i : S^{m-1} → ℝ^m \ {0}. -/
def sphereToPunctured (y : UnitSphere m) : PuncturedSpace m :=
  ⟨y.val, by
    have h : dist y.val (0 : EuclideanSpace ℝ (Fin m)) = 1 := y.property
    have h_norm : ‖y.val‖ = 1 := by
      simp
    have h' : y.val ≠ 0 := by
      intro h''
      rw [h''] at h_norm
      simp at h_norm
    exact h'⟩

end Maps

section Continuity

/-- The retraction map is continuous. -/
lemma continuous_puncturedToSphere : Continuous (puncturedToSphere (m := m)) := by
  have h_main : Continuous (fun (x : PuncturedSpace m) => (1 / ‖x.val‖) • x.val) := by
    have h_norm : Continuous (fun (x : PuncturedSpace m) => ‖x.val‖) :=
      continuous_norm.comp continuous_subtype_val
    have h1 : Continuous (fun (x : PuncturedSpace m) => (1 : ℝ) / ‖x.val‖) := by
      exact continuous_const.div h_norm (fun x => (norm_pos_iff.mpr x.property).ne')
    exact h1.smul continuous_subtype_val
  have h : Continuous (fun (x : PuncturedSpace m) => (puncturedToSphere x : EuclideanSpace ℝ (Fin m))) :=
    h_main
  exact Continuous.subtype_mk h _

/-- The inclusion map is continuous. -/
lemma continuous_sphereToPunctured : Continuous (sphereToPunctured (m := m)) :=
  Isometry.continuous fun _ => congrFun rfl

end Continuity

section DeformationRetraction

/-- The scalar factor for the deformation retraction: (1-t) + t/‖x‖. -/
def retractionScaling (x : PuncturedSpace m) (t : ℝ) : ℝ :=
  (1 - t) + t / ‖x.val‖

lemma retractionScaling_pos (x : PuncturedSpace m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < retractionScaling x t := by
  have h₁ : 0 < ‖x.val‖ := norm_pos_iff.mpr x.property
  have h₂ : 0 ≤ 1 - t := by linarith
  have h₃ : 0 ≤ t / ‖x.val‖ := by
    exact div_nonneg ht0 (le_of_lt h₁)
  by_cases h : t = 0
  · rw [retractionScaling, h] ; norm_num
  · have h_pos : 0 < t := by
      exact lt_of_le_of_ne ht0 (Ne.symm h)
    have h_pos2 : 0 < t / ‖x.val‖ := div_pos h_pos h₁
    dsimp only [retractionScaling]
    linarith

/-- The unit interval I = [0,1] as a subtype. -/
abbrev PuncturedIcc01 : Type _ := {t : ℝ // 0 ≤ t ∧ t ≤ 1}

/-- The deformation retraction H : (ℝ^m \\ {0}) × I → ℝ^m \\ {0}.
    H(x, t) = ((1-t) + t/‖x‖) • x -/
def deformationMap (p : PuncturedSpace m × PuncturedIcc01) : PuncturedSpace m :=
  let x := p.1
  let t : ℝ := p.2.val
  let ht0 : 0 ≤ t := p.2.property.1
  let ht1 : t ≤ 1 := p.2.property.2
  let s : ℝ := retractionScaling x t
  ⟨s • x.val, by
    have h_pos : 0 < s := retractionScaling_pos x t ht0 ht1
    have h_ne : s • x.val ≠ 0 := by
      intro h
      have h' : x.val = 0 := (smul_eq_zero).mp h |>.resolve_left (ne_of_gt h_pos)
      exact x.property h'
    exact h_ne⟩

/-- The deformation map is continuous. -/
lemma continuous_deformationMap : Continuous (deformationMap (m := m)) := by
  have h_main : Continuous (fun (p : PuncturedSpace m × PuncturedIcc01) =>
      retractionScaling p.1 p.2.val • p.1.val) := by
    have h1 : Continuous (fun (p : PuncturedSpace m × PuncturedIcc01) => retractionScaling p.1 p.2.val) := by
      have h_t : Continuous (fun (p : PuncturedSpace m × PuncturedIcc01) => (p.2.val : ℝ)) :=
        continuous_subtype_val.comp continuous_snd
      have h_norm : Continuous (fun (p : PuncturedSpace m × PuncturedIcc01) => ‖p.1.val‖) :=
        continuous_norm.comp (continuous_subtype_val.comp continuous_fst)
      have h_const1 : Continuous (fun (_ : PuncturedSpace m × PuncturedIcc01) => (1 : ℝ)) := continuous_const
      exact (h_const1.sub h_t).add (h_t.div h_norm (fun p => (norm_pos_iff.mpr p.1.property).ne'))
    have h_x : Continuous (fun (p : PuncturedSpace m × PuncturedIcc01) => p.1.val) :=
      continuous_subtype_val.comp continuous_fst
    exact h1.smul h_x
  have h : Continuous (fun (p : PuncturedSpace m × PuncturedIcc01) =>
      (deformationMap p : EuclideanSpace ℝ (Fin m))) := h_main
  exact Continuous.subtype_mk h _

/-- At t=0, the deformation is the identity. -/
lemma deformationMap_zero (x : PuncturedSpace m) :
    deformationMap (m := m) (x, ⟨0, by constructor <;> norm_num⟩) = x := by
  apply Subtype.ext
  simp [deformationMap, retractionScaling]

/-- At t=1, the deformation is the retraction onto the sphere. -/
lemma deformationMap_one (x : PuncturedSpace m) :
    deformationMap (m := m) (x, ⟨1, by constructor <;> norm_num⟩) =
    sphereToPunctured (puncturedToSphere x) := by
  apply Subtype.ext
  simp [deformationMap, retractionScaling, puncturedToSphere, sphereToPunctured]


end DeformationRetraction

section HomotopyEquiv

/-- The composite `puncturedToSphere ∘ sphereToPunctured` is the identity on the sphere. -/
lemma sphere_punctured_sphere (y : UnitSphere m) :
    puncturedToSphere (sphereToPunctured y) = y := by
  apply Subtype.ext
  have h_norm : ‖y.val‖ = 1 := by
    have h : dist y.val (0 : EuclideanSpace ℝ (Fin m)) = 1 := y.property
    simp
  have h : ‖(1 / ‖y.val‖) • y.val‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (show 0 ≤ 1 / ‖y.val‖ from by positivity)]
    ; rw [h_norm] ; field_simp
  have h' : dist ((1 / ‖y.val‖) • y.val) (0 : EuclideanSpace ℝ (Fin m)) = 1 := by
    simp [dist_zero_right]
  simp [puncturedToSphere, sphereToPunctured]

/-- The deformation retraction as a map `unitInterval × PuncturedSpace m → PuncturedSpace m`. -/
def deformationMap' (p : ↥unitInterval × PuncturedSpace m) : PuncturedSpace m :=
  let t : ℝ := p.1.val
  let x := p.2
  let ht0 : 0 ≤ t := p.1.prop.1
  let ht1 : t ≤ 1 := p.1.prop.2
  let s : ℝ := retractionScaling x t
  ⟨s • x.val, by
    have h_pos : 0 < s := retractionScaling_pos x t ht0 ht1
    have h_ne : s • x.val ≠ 0 := by
      intro h
      have h' : x.val = 0 := (smul_eq_zero).mp h |>.resolve_left (ne_of_gt h_pos)
      exact x.property h'
    exact h_ne⟩

/-- The deformation map is continuous. -/
lemma continuous_deformationMap' : Continuous (deformationMap' (m := m)) := by
  have h_main : Continuous (fun (p : ↥unitInterval × PuncturedSpace m) =>
      retractionScaling p.2 p.1.val • p.2.val) := by
    have h_t : Continuous (fun (p : ↥unitInterval × PuncturedSpace m) => (p.1.val : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have h_norm : Continuous (fun (p : ↥unitInterval × PuncturedSpace m) => ‖p.2.val‖) :=
      continuous_norm.comp (continuous_subtype_val.comp continuous_snd)
    have h_const1 : Continuous (fun (_ : ↥unitInterval × PuncturedSpace m) => (1 : ℝ)) := continuous_const
    have h1 : Continuous (fun (p : ↥unitInterval × PuncturedSpace m) => retractionScaling p.2 p.1.val) :=
      (h_const1.sub h_t).add (h_t.div h_norm (fun p => (norm_pos_iff.mpr p.2.property).ne'))
    have h_x : Continuous (fun (p : ↥unitInterval × PuncturedSpace m) => p.2.val) :=
      continuous_subtype_val.comp continuous_snd
    exact h1.smul h_x
  have h : Continuous (fun (p : ↥unitInterval × PuncturedSpace m) =>
      (deformationMap' p : EuclideanSpace ℝ (Fin m))) := h_main
  exact Continuous.subtype_mk h _

/-- Homotopy from the identity to `sphereToPunctured ∘ puncturedToSphere`. -/
def idHomotopy : ContinuousMap.Homotopy
    (ContinuousMap.id (PuncturedSpace m))
    (ContinuousMap.mk (sphereToPunctured ∘ puncturedToSphere)
      (continuous_sphereToPunctured.comp continuous_puncturedToSphere)) :=
  { toFun := deformationMap'
    continuous_toFun := continuous_deformationMap'
    map_zero_left := fun x => by
      apply Subtype.ext
      simp [deformationMap', retractionScaling]
    map_one_left := fun x => by
      apply Subtype.ext
      simp [deformationMap', retractionScaling, puncturedToSphere, sphereToPunctured]
        }

/-- Homotopy equivalence between the punctured space and the sphere. -/
noncomputable def puncturedSphereHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (PuncturedSpace m) (UnitSphere m) := by
  let f : ContinuousMap (PuncturedSpace m) (UnitSphere m) :=
    ⟨puncturedToSphere, continuous_puncturedToSphere⟩
  let g : ContinuousMap (UnitSphere m) (PuncturedSpace m) :=
    ⟨sphereToPunctured, continuous_sphereToPunctured⟩
  have h_left : (g.comp f).Homotopic (ContinuousMap.id (PuncturedSpace m)) := by
    refine' ⟨idHomotopy.symm⟩
  have h_right : (f.comp g).Homotopic (ContinuousMap.id (UnitSphere m)) := by
    have h_eq : f.comp g = ContinuousMap.id (UnitSphere m) := by
      apply ContinuousMap.ext
      intro y
      simpa [f, g] using sphere_punctured_sphere y
    rw [h_eq]
  exact ⟨f, g, h_left, h_right⟩

end HomotopyEquiv

section ExteriorBall

/-- The exterior of the closed unit ball: {x ∈ ℝ^m | ‖x‖ > 1}. -/
abbrev ExteriorBall (m : ℕ) [Nonempty (Fin m)] : Type _ :=
  {x : EuclideanSpace ℝ (Fin m) // 1 < ‖x‖}

section Maps

/-- The inclusion of the exterior ball into the punctured space.

    Since ‖x‖ > 1 implies x ≠ 0. -/
def exteriorToPunctured (x : ExteriorBall m) : PuncturedSpace m :=
  ⟨x.val, by
    have h₁ : 1 < ‖x.val‖ := x.property
    have h₂ : 0 < ‖x.val‖ := by linarith
    exact norm_pos_iff.mp h₂⟩

/-- The map from punctured space to exterior ball: x ↦ x * (1 + 1/‖x‖) = x + x/‖x‖.

    This maps any nonzero point to a point with norm ‖x‖ + 1 > 1. -/
def puncturedToExterior (x : PuncturedSpace m) : ExteriorBall m :=
  let s : ℝ := 1 + 1 / ‖x.val‖
  ⟨s • x.val, by
    have h₁ : 0 < ‖x.val‖ := norm_pos_iff.mpr x.property
    have h₂ : ‖s • x.val‖ = s * ‖x.val‖ := by
      rw [norm_smul, Real.norm_of_nonneg (show 0 ≤ s from by positivity)]
    have h₃ : 1 < s * ‖x.val‖ := by
      dsimp only [s]
      have h₄ : (1 + 1 / ‖x.val‖) * ‖x.val‖ = ‖x.val‖ + 1 := by
        field_simp [h₁.ne']
      rw [h₄]
      linarith
    rw [h₂]
    exact h₃⟩

/-- The inclusion map is continuous. -/
lemma continuous_exteriorToPunctured : Continuous (exteriorToPunctured (m := m)) := by
  have h : Continuous (fun (x : ExteriorBall m) => (x.val : EuclideanSpace ℝ (Fin m))) :=
    continuous_subtype_val
  exact Continuous.subtype_mk h _

/-- The map `puncturedToExterior` is continuous. -/
lemma continuous_puncturedToExterior : Continuous (puncturedToExterior (m := m)) := by
  have h_main : Continuous (fun (x : PuncturedSpace m) => (1 + 1 / ‖x.val‖) • x.val) := by
    have h_norm : Continuous (fun (x : PuncturedSpace m) => ‖x.val‖) :=
      continuous_norm.comp continuous_subtype_val
    have h1 : Continuous (fun (x : PuncturedSpace m) => (1 : ℝ) / ‖x.val‖) := by
      exact continuous_const.div h_norm (fun x => (norm_pos_iff.mpr x.property).ne')
    have h2 : Continuous (fun (x : PuncturedSpace m) => (1 : ℝ) + 1 / ‖x.val‖) := by
      exact continuous_const.add h1
    exact h2.smul continuous_subtype_val
  have h : Continuous (fun (x : PuncturedSpace m) => (puncturedToExterior x : EuclideanSpace ℝ (Fin m))) :=
    h_main
  exact Continuous.subtype_mk h _

end Maps

section DeformationRetraction

/-- The scalar factor for the deformation: (1 + t/‖x‖). -/
def exteriorScaling (x : PuncturedSpace m) (t : ℝ) : ℝ :=
  1 + t / ‖x.val‖

/-- The deformation homotopy from id to `exteriorToPunctured ∘ puncturedToExterior`.

    H(x, t) = (1 + t/‖x‖) • x
    - H(x, 0) = x
    - H(x, 1) = (1 + 1/‖x‖) • x = puncturedToExterior x (in the punctured space) -/
def puncturedExteriorHomotopy (p : ↥unitInterval × PuncturedSpace m) : PuncturedSpace m :=
  let t : ℝ := p.1.val
  let x := p.2
  let s : ℝ := exteriorScaling x t
  ⟨s • x.val, by
    have h₁ : 0 < ‖x.val‖ := norm_pos_iff.mpr x.property
    have ht0 : 0 ≤ t := p.1.prop.1
    have h₂ : 0 ≤ t / ‖x.val‖ := by positivity
    have h₃ : 0 < s := by
      dsimp only [s, exteriorScaling]
      linarith
    have h₄ : s • x.val ≠ 0 := by
      intro h₅
      have h₆ : x.val = 0 := (smul_eq_zero).mp h₅ |>.resolve_left (ne_of_gt h₃)
      have h₇ : ‖x.val‖ = 0 := by rw [h₆] ; simp
      exact h₁.ne' h₇
    exact h₄⟩

/-- Continuity of the deformation homotopy. -/
lemma continuous_puncturedExteriorHomotopy :
    Continuous (fun p : ↥unitInterval × PuncturedSpace m => puncturedExteriorHomotopy p) := by
  have h_main : Continuous (fun (p : ↥unitInterval × PuncturedSpace m) =>
      (exteriorScaling p.2 (p.1.val)) • (p.2.val)) := by
    have h_t : Continuous (fun (p : ↥unitInterval × PuncturedSpace m) => (p.1.val : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have h_norm : Continuous (fun (p : ↥unitInterval × PuncturedSpace m) => ‖p.2.val‖) :=
      continuous_norm.comp (continuous_subtype_val.comp continuous_snd)
    have h_const1 : Continuous (fun (_ : ↥unitInterval × PuncturedSpace m) => (1 : ℝ)) := continuous_const
    have h1 : Continuous (fun (p : ↥unitInterval × PuncturedSpace m) => exteriorScaling p.2 p.1.val) := by
      have := h_const1.add (h_t.div h_norm (fun p => (norm_pos_iff.mpr p.2.property).ne'))
      exact this.congr (fun p => by simp [exteriorScaling])
    have h_x : Continuous (fun (p : ↥unitInterval × PuncturedSpace m) => p.2.val) :=
      continuous_subtype_val.comp continuous_snd
    exact h1.smul h_x
  have h : Continuous (fun (p : ↥unitInterval × PuncturedSpace m) =>
      (puncturedExteriorHomotopy p : EuclideanSpace ℝ (Fin m))) := h_main
  exact Continuous.subtype_mk h _

/-- At t=0, the homotopy is the identity. -/
lemma puncturedExteriorHomotopy_zero (x : PuncturedSpace m) :
    puncturedExteriorHomotopy (0, x) = x := by
  apply Subtype.ext
  simp [puncturedExteriorHomotopy, exteriorScaling]

/-- At t=1, the homotopy is `exteriorToPunctured ∘ puncturedToExterior`. -/
lemma puncturedExteriorHomotopy_one (x : PuncturedSpace m) :
    puncturedExteriorHomotopy (1, x) = (exteriorToPunctured (puncturedToExterior x)) := by
  apply Subtype.ext
  simp [puncturedExteriorHomotopy, exteriorScaling, puncturedToExterior, exteriorToPunctured]

end DeformationRetraction

section ExteriorDeformationRetraction

/-- The scalar factor for the deformation on the exterior ball: (1 + (1-t)/‖x‖). -/
def exteriorBallScaling (x : ExteriorBall m) (t : ℝ) : ℝ :=
  1 + (1 - t) / ‖x.val‖

/-- The deformation homotopy from `puncturedToExterior ∘ exteriorToPunctured` to `id`
    on the exterior ball.

    H(x, t) = (1 + (1-t)/‖x‖) • x
    - H(x, 0) = (1 + 1/‖x‖) • x = g(f(x))
    - H(x, 1) = x -/
def exteriorPuncturedHomotopy (p : ↥unitInterval × ExteriorBall m) : ExteriorBall m :=
  let t : ℝ := p.1.val
  let x := p.2
  let s : ℝ := exteriorBallScaling x t
  ⟨s • x.val, by
    have h₁ : 1 < ‖x.val‖ := x.property
    have ht0 : 0 ≤ t := p.1.prop.1
    have ht1 : t ≤ 1 := p.1.prop.2
    have h₂ : 0 ≤ 1 - t := by linarith
    have h_pos_norm : 0 < ‖x.val‖ := by linarith
    have h₃ : 0 ≤ (1 - t) / ‖x.val‖ := by positivity
    have h_s_nonneg : 0 ≤ s := by
      dsimp only [s, exteriorBallScaling]
      linarith
    have h₄ : ‖s • x.val‖ = s * ‖x.val‖ := by
      rw [norm_smul, Real.norm_of_nonneg h_s_nonneg]
    have h₅ : s * ‖x.val‖ = ‖x.val‖ + (1 - t) := by
      dsimp only [s, exteriorBallScaling]
      have h_pos : 0 < ‖x.val‖ := by linarith
      field_simp [h_pos.ne']
    have h₆ : 1 < s * ‖x.val‖ := by
      rw [h₅]
      linarith
    rw [h₄]
    exact h₆⟩

/-- Continuity of the exterior ball deformation homotopy. -/
lemma continuous_exteriorPuncturedHomotopy :
    Continuous (fun p : ↥unitInterval × ExteriorBall m => exteriorPuncturedHomotopy p) := by
  have h_main : Continuous (fun (p : ↥unitInterval × ExteriorBall m) =>
      (exteriorBallScaling p.2 (p.1.val)) • (p.2.val)) := by
    have h_t : Continuous (fun (p : ↥unitInterval × ExteriorBall m) => (p.1.val : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have h_norm : Continuous (fun (p : ↥unitInterval × ExteriorBall m) => ‖p.2.val‖) :=
      continuous_norm.comp (continuous_subtype_val.comp continuous_snd)
    have h_const1 : Continuous (fun (_ : ↥unitInterval × ExteriorBall m) => (1 : ℝ)) := continuous_const
    have h1 : Continuous (fun (p : ↥unitInterval × ExteriorBall m) => (1 - p.1.val : ℝ)) := by
      exact continuous_const.sub h_t
    have h2 : Continuous (fun (p : ↥unitInterval × ExteriorBall m) => exteriorBallScaling p.2 p.1.val) := by
      have := h_const1.add (h1.div h_norm (fun p => (lt_trans (by norm_num) p.2.property).ne'))
      exact this.congr (fun p => by simp [exteriorBallScaling])
    have h_x : Continuous (fun (p : ↥unitInterval × ExteriorBall m) => p.2.val) :=
      continuous_subtype_val.comp continuous_snd
    exact h2.smul h_x
  have h : Continuous (fun (p : ↥unitInterval × ExteriorBall m) =>
      (exteriorPuncturedHomotopy p : EuclideanSpace ℝ (Fin m))) := h_main
  exact Continuous.subtype_mk h _

/-- At t=0, the homotopy is `puncturedToExterior ∘ exteriorToPunctured`. -/
lemma exteriorPuncturedHomotopy_zero (x : ExteriorBall m) :
    exteriorPuncturedHomotopy (0, x) = puncturedToExterior (exteriorToPunctured x) := by
  apply Subtype.ext
  simp [exteriorPuncturedHomotopy, exteriorBallScaling, puncturedToExterior, exteriorToPunctured]

/-- At t=1, the homotopy is the identity. -/
lemma exteriorPuncturedHomotopy_one (x : ExteriorBall m) :
    exteriorPuncturedHomotopy (1, x) = x := by
  apply Subtype.ext
  simp [exteriorPuncturedHomotopy, exteriorBallScaling]

end ExteriorDeformationRetraction

section HomotopyEquiv

/-- Homotopy equivalence between the exterior ball and the punctured space. -/
noncomputable def exteriorBallPuncturedHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ExteriorBall m) (PuncturedSpace m) := by
  let f : ContinuousMap (ExteriorBall m) (PuncturedSpace m) :=
    ⟨exteriorToPunctured, continuous_exteriorToPunctured⟩
  let g : ContinuousMap (PuncturedSpace m) (ExteriorBall m) :=
    ⟨puncturedToExterior, continuous_puncturedToExterior⟩
  have h_right : (f.comp g).Homotopic (ContinuousMap.id (PuncturedSpace m)) := by
    let H_id_to_fg : ContinuousMap.Homotopy (ContinuousMap.id (PuncturedSpace m)) (f.comp g) :=
      { toFun := puncturedExteriorHomotopy
        continuous_toFun := continuous_puncturedExteriorHomotopy
        map_zero_left := puncturedExteriorHomotopy_zero
        map_one_left := puncturedExteriorHomotopy_one }
    exact ⟨H_id_to_fg.symm⟩
  have h_left : (g.comp f).Homotopic (ContinuousMap.id (ExteriorBall m)) := by
    let H_gf_to_id : ContinuousMap.Homotopy (g.comp f) (ContinuousMap.id (ExteriorBall m)) :=
      { toFun := exteriorPuncturedHomotopy
        continuous_toFun := continuous_exteriorPuncturedHomotopy
        map_zero_left := exteriorPuncturedHomotopy_zero
        map_one_left := exteriorPuncturedHomotopy_one }
    exact ⟨H_gf_to_id⟩
  exact ⟨f, g, h_left, h_right⟩

end HomotopyEquiv

end ExteriorBall

end Topology.EuclideanSpace

end section
