import MyLeanRepo.Kakeya.CV.Geometry
import Mathlib.Tactic

/-!
# Shape space for ellipsoid colouring

Centered ellipsoids in `Point 3` are identified with invertible linear maps
`A : Point 3 ≃ₗ[ℝ] Point 3`.  This module defines a closeness relation
`ShapeClose β A₁ A₂` and proves the structural properties needed for the
graph-colouring argument of Carbery--Valdimarsson Lemma 8.
-/

noncomputable section

open Kakeya.CV

namespace Kakeya.CV.ShapeSpace

/-- Embed a linear equivalence into continuous linear maps for norm access. -/
noncomputable def clm (A : Point 3 ≃ₗ[ℝ] Point 3) : Point 3 →L[ℝ] Point 3 :=
  A.toContinuousLinearEquiv.toContinuousLinearMap

lemma clm_injective : Function.Injective clm := by
  intro A B h
  exact LinearEquiv.ext (fun x => by
    simpa [clm] using congr_arg (fun (f : Point 3 →L[ℝ] Point 3) => f x) h)

lemma clm_trans (A B : Point 3 ≃ₗ[ℝ] Point 3) :
    clm (A.trans B) = (clm B).comp (clm A) := by
  ext x
  simp [clm, LinearEquiv.trans_apply]

lemma clm_one : clm (1 : Point 3 ≃ₗ[ℝ] Point 3) = 1 := by
  ext x
  simp [clm]

/-- Two shapes are `β`-close if relative distortion both ways is ≤ `β`. -/
def ShapeClose (β : ℝ) (A₁ A₂ : Point 3 ≃ₗ[ℝ] Point 3) : Prop :=
  ‖clm (A₁.symm.trans A₂)‖ ≤ β ∧ ‖clm (A₂.symm.trans A₁)‖ ≤ β

lemma shapeClose_symm {β : ℝ} {A₁ A₂ : Point 3 ≃ₗ[ℝ] Point 3} :
    ShapeClose β A₁ A₂ ↔ ShapeClose β A₂ A₁ := by
  simp [ShapeClose, and_comm]

lemma shapeClose_refl {β : ℝ} (hβ : 1 ≤ β) {A : Point 3 ≃ₗ[ℝ] Point 3} :
    ShapeClose β A A := by
  have h_eq : A.symm.trans A = (1 : Point 3 ≃ₗ[ℝ] Point 3) := A.symm_trans_self
  have h1 : ‖clm (A.symm.trans A)‖ = 1 := by
    rw [h_eq, clm_one]
    exact norm_one
  exact ⟨by rw [h1]; exact hβ, by rw [h1]; exact hβ⟩

lemma shapeClose_trans {β γ : ℝ} {A₁ A₂ A₃ : Point 3 ≃ₗ[ℝ] Point 3}
    (h1 : ShapeClose β A₁ A₂) (h2 : ShapeClose γ A₂ A₃) :
    ShapeClose (β * γ) A₁ A₃ := by
  have h_eq1 : A₁.symm.trans A₃ = (A₁.symm.trans A₂).trans (A₂.symm.trans A₃) := by
    ext x; simp [LinearEquiv.trans_apply]
  have h_dir1 : ‖clm (A₁.symm.trans A₃)‖ ≤ β * γ := by
    calc
      ‖clm (A₁.symm.trans A₃)‖
        = ‖(clm (A₂.symm.trans A₃)).comp (clm (A₁.symm.trans A₂))‖ := by
          rw [h_eq1, clm_trans]
      _ ≤ ‖clm (A₂.symm.trans A₃)‖ * ‖clm (A₁.symm.trans A₂)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ γ * β := by
          have ha : ‖clm (A₂.symm.trans A₃)‖ ≤ γ := h2.1
          have hb : ‖clm (A₁.symm.trans A₂)‖ ≤ β := h1.1
          nlinarith [norm_nonneg (clm (A₂.symm.trans A₃)), norm_nonneg (clm (A₁.symm.trans A₂))]
      _ = β * γ := by ring
  have h_eq2 : A₃.symm.trans A₁ = (A₃.symm.trans A₂).trans (A₂.symm.trans A₁) := by
    ext x; simp [LinearEquiv.trans_apply]
  have h_dir2 : ‖clm (A₃.symm.trans A₁)‖ ≤ β * γ := by
    calc
      ‖clm (A₃.symm.trans A₁)‖
        = ‖(clm (A₂.symm.trans A₁)).comp (clm (A₃.symm.trans A₂))‖ := by
          rw [h_eq2, clm_trans]
      _ ≤ ‖clm (A₂.symm.trans A₁)‖ * ‖clm (A₃.symm.trans A₂)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ β * γ := by
          have ha : ‖clm (A₂.symm.trans A₁)‖ ≤ β := h1.2
          have hb : ‖clm (A₃.symm.trans A₂)‖ ≤ γ := h2.2
          nlinarith [norm_nonneg (clm (A₂.symm.trans A₁)), norm_nonneg (clm (A₃.symm.trans A₂))]
  exact ⟨h_dir1, h_dir2⟩

lemma shapeClose_mul_left {β : ℝ} {A₀ A₁ A₂ : Point 3 ≃ₗ[ℝ] Point 3}
    (h : ShapeClose β A₁ A₂) :
    ShapeClose β (A₀.trans A₁) (A₀.trans A₂) := by
  have h3 : (A₀.trans A₁).symm.trans (A₀.trans A₂) = A₁.symm.trans A₂ := by
    ext x; simp [LinearEquiv.trans_apply]
  have h4 : (A₀.trans A₂).symm.trans (A₀.trans A₁) = A₂.symm.trans A₁ := by
    ext x; simp [LinearEquiv.trans_apply]
  rw [ShapeClose, h3, h4]
  exact h

/-- Aspect ratio (condition number) of a shape. -/
def aspectRatio (A : Point 3 ≃ₗ[ℝ] Point 3) : ℝ :=
  ‖clm A‖ * ‖clm A.symm‖

lemma shapeClose_id_aspectRatio {β : ℝ} (hβ : 0 ≤ β) {A : Point 3 ≃ₗ[ℝ] Point 3} :
    ShapeClose β (1 : Point 3 ≃ₗ[ℝ] Point 3) A → aspectRatio A ≤ β ^ 2 := by
  intro h
  have h1 : ‖clm A‖ ≤ β := h.1
  have h2 : ‖clm A.symm‖ ≤ β := h.2
  dsimp only [aspectRatio]
  calc
    ‖clm A‖ * ‖clm A.symm‖ ≤ β * ‖clm A.symm‖ := by gcongr
    _ ≤ β * β := by gcongr
    _ = β ^ 2 := by ring

/-- Image of bounded-aspect-ratio shapes in CLM space. -/
def boundedShapeImage (C : ℝ) : Set (Point 3 →L[ℝ] Point 3) :=
  clm '' {A | ShapeClose C 1 A}

-- Auxiliary set in product space
private def auxSet (C : ℝ) :
    Set ((Point 3 →L[ℝ] Point 3) × (Point 3 →L[ℝ] Point 3)) :=
  {p | ‖p.1‖ ≤ C ∧ ‖p.2‖ ≤ C ∧ p.1 * p.2 = 1 ∧ p.2 * p.1 = 1}

private lemma auxSet_closed {C : ℝ} (hC : 0 ≤ C) : IsClosed (auxSet C) := by
  have h1 : Continuous (fun p : (Point 3 →L[ℝ] Point 3) × (Point 3 →L[ℝ] Point 3) => ‖p.1‖) :=
    continuous_norm.comp continuous_fst
  have h2 : Continuous (fun p : (Point 3 →L[ℝ] Point 3) × (Point 3 →L[ℝ] Point 3) => ‖p.2‖) :=
    continuous_norm.comp continuous_snd
  have h3 : Continuous (fun p : (Point 3 →L[ℝ] Point 3) × (Point 3 →L[ℝ] Point 3) => p.1 * p.2) :=
    continuous_fst.mul continuous_snd
  have h4 : Continuous (fun p : (Point 3 →L[ℝ] Point 3) × (Point 3 →L[ℝ] Point 3) => p.2 * p.1) :=
    continuous_snd.mul continuous_fst
  have h_set : auxSet C =
      {p : (Point 3 →L[ℝ] Point 3) × (Point 3 →L[ℝ] Point 3) | ‖p.1‖ ≤ C} ∩
      {p : (Point 3 →L[ℝ] Point 3) × (Point 3 →L[ℝ] Point 3) | ‖p.2‖ ≤ C} ∩
      {p : (Point 3 →L[ℝ] Point 3) × (Point 3 →L[ℝ] Point 3) | p.1 * p.2 = 1} ∩
      {p : (Point 3 →L[ℝ] Point 3) × (Point 3 →L[ℝ] Point 3) | p.2 * p.1 = 1} := by
    ext p; simp [auxSet]; tauto
  rw [h_set]
  exact (isClosed_le h1 continuous_const).inter (isClosed_le h2 continuous_const)
    |>.inter (isClosed_eq h3 continuous_const)
    |>.inter (isClosed_eq h4 continuous_const)

private lemma auxSet_bounded {C : ℝ} (hC : 0 ≤ C) : Bornology.IsBounded (auxSet C) := by
  have h_sub : auxSet C ⊆ Metric.closedBall (0 : _) (max C C) := by
    intro p hp
    have h1 : ‖p.1‖ ≤ C := hp.1
    have h2 : ‖p.2‖ ≤ C := hp.2.1
    have h3 : ‖p‖ ≤ max C C := by
      have h4 : ‖p‖ = max ‖p.1‖ ‖p.2‖ := by
        simp [Prod.norm_def] <;> rfl
      rw [h4]
      exact max_le_max h1 h2
    simpa [Metric.mem_closedBall] using h3
  exact Metric.isBounded_closedBall.subset h_sub

private lemma auxSet_compact {C : ℝ} (hC : 0 ≤ C) : IsCompact (auxSet C) := by
  haveI : ProperSpace ((Point 3 →L[ℝ] Point 3) × (Point 3 →L[ℝ] Point 3)) := by
    exact prod_properSpace
  exact Metric.isCompact_of_isClosed_isBounded (auxSet_closed hC) (auxSet_bounded hC)

private lemma boundedShapeImage_eq_projection {C : ℝ} (hC : 0 ≤ C) :
    boundedShapeImage C = Prod.fst '' auxSet C := by
  ext f
  simp only [boundedShapeImage, auxSet, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨A, hA, rfl⟩
    have h_eq1 : clm (A.symm.trans A) = (clm A).comp (clm A.symm) := clm_trans A.symm A
    have h_eq2 : clm (A.trans A.symm) = (clm A.symm).comp (clm A) := clm_trans A A.symm
    have h_id1 : clm (A.symm.trans A) = 1 := by
      have h : A.symm.trans A = (1 : Point 3 ≃ₗ[ℝ] Point 3) := A.symm_trans_self
      calc
        clm (A.symm.trans A) = clm (1 : Point 3 ≃ₗ[ℝ] Point 3) := by rw [h]
        _ = 1 := clm_one
    have h_id2 : clm (A.trans A.symm) = 1 := by
      have h : A.trans A.symm = (1 : Point 3 ≃ₗ[ℝ] Point 3) := A.self_trans_symm
      calc
        clm (A.trans A.symm) = clm (1 : Point 3 ≃ₗ[ℝ] Point 3) := by rw [h]
        _ = 1 := clm_one
    have hfg : (clm A).comp (clm A.symm) = 1 := Eq.trans h_eq1.symm h_id1
    have hgf : (clm A.symm).comp (clm A) = 1 := Eq.trans h_eq2.symm h_id2
    exact ⟨(clm A, clm A.symm), ⟨hA.1, hA.2, hfg, hgf⟩, rfl⟩
  · rintro ⟨⟨f, g⟩, ⟨hfnorm, hgnorm, hfg, hgf⟩, rfl⟩
    let e : Point 3 ≃ₗ[ℝ] Point 3 :=
      { toFun := f,
        invFun := g,
        left_inv := fun x => by
          have h : g (f x) = x := by
            simpa using congr_arg (fun (h : Point 3 →L[ℝ] Point 3) => h x) hgf
          exact h,
        right_inv := fun x => by
          have h : f (g x) = x := by
            simpa using congr_arg (fun (h : Point 3 →L[ℝ] Point 3) => h x) hfg
          exact h,
        map_add' := f.map_add,
        map_smul' := f.map_smul }
    have hclm : clm e = f := by ext x; rfl
    have hclm_symm : clm e.symm = g := by ext x; simp [clm, e]
    have hA : ShapeClose C (1 : Point 3 ≃ₗ[ℝ] Point 3) e := by
      have h5 : ‖clm e‖ ≤ C := by rw [hclm]; exact hfnorm
      have h6 : ‖clm e.symm‖ ≤ C := by rw [hclm_symm]; exact hgnorm
      exact ⟨h5, h6⟩
    exact ⟨e, hA, hclm⟩

lemma boundedShapeImage_compact {C : ℝ} (hC : 0 ≤ C) :
    IsCompact (boundedShapeImage C) := by
  rw [boundedShapeImage_eq_projection hC]
  exact (auxSet_compact hC).image continuous_fst

/-- If two shapes in the bounded-aspect-ratio set are sufficiently close in
operator norm (distance ≤ (α-1)/C), then they are `α`-close in the
`ShapeClose` sense. -/
lemma operatorNormClose_imp_shapeClose {α C : ℝ} (hα : 1 < α) (hC : 0 < C)
    {A₁ A₂ : Point 3 ≃ₗ[ℝ] Point 3}
    (h1 : ShapeClose C 1 A₁) (h2 : ShapeClose C 1 A₂)
    (hdist : ‖clm A₁ - clm A₂‖ ≤ (α - 1) / C) :
    ShapeClose α A₁ A₂ := by
  set δ := (α - 1) / C with hδ_def
  have hδ_nonneg : 0 ≤ δ := by positivity
  have h_inv1 : ‖clm A₁.symm‖ ≤ C := h1.2
  have h_inv2 : ‖clm A₂.symm‖ ≤ C := h2.2
  have h_eq1 : clm (A₁.symm.trans A₁) = (clm A₁).comp (clm A₁.symm) := clm_trans A₁.symm A₁
  have h_id1 : clm (A₁.symm.trans A₁) = 1 := by
    have h : A₁.symm.trans A₁ = (1 : Point 3 ≃ₗ[ℝ] Point 3) := A₁.symm_trans_self
    calc
      clm (A₁.symm.trans A₁) = clm (1 : Point 3 ≃ₗ[ℝ] Point 3) := by rw [h]
      _ = 1 := clm_one
  have hfg1 : (clm A₁).comp (clm A₁.symm) = 1 := Eq.trans h_eq1.symm h_id1
  have h_eq2 : clm (A₂.symm.trans A₂) = (clm A₂).comp (clm A₂.symm) := clm_trans A₂.symm A₂
  have h_id2 : clm (A₂.symm.trans A₂) = 1 := by
    have h : A₂.symm.trans A₂ = (1 : Point 3 ≃ₗ[ℝ] Point 3) := A₂.symm_trans_self
    calc
      clm (A₂.symm.trans A₂) = clm (1 : Point 3 ≃ₗ[ℝ] Point 3) := by rw [h]
      _ = 1 := clm_one
  have hfg2 : (clm A₂).comp (clm A₂.symm) = 1 := Eq.trans h_eq2.symm h_id2
  have h_symm : ‖clm A₂ - clm A₁‖ = ‖clm A₁ - clm A₂‖ := by
    have h : clm A₂ - clm A₁ = -(clm A₁ - clm A₂) := by abel
    rw [h, norm_neg]
  -- First direction
  have h_dir1 : ‖(clm A₂).comp (clm A₁.symm)‖ ≤ α := by
    have h_decomp : (clm A₂).comp (clm A₁.symm) =
        (clm A₁).comp (clm A₁.symm) + (clm A₂ - clm A₁).comp (clm A₁.symm) := by
      have h : clm A₂ = clm A₁ + (clm A₂ - clm A₁) := by abel
      rw [h]
      simp [ContinuousLinearMap.add_comp] <;> rfl
    have h_goal : ‖(clm A₂).comp (clm A₁.symm)‖ ≤ α := by
      rw [h_decomp]
      rw [hfg1]
      have h_bound : ‖(clm A₂ - clm A₁).comp (clm A₁.symm)‖ ≤
          ‖clm A₂ - clm A₁‖ * ‖clm A₁.symm‖ := ContinuousLinearMap.opNorm_comp_le _ _
      calc
        ‖(1 : Point 3 →L[ℝ] Point 3) + (clm A₂ - clm A₁).comp (clm A₁.symm)‖
          ≤ ‖(1 : Point 3 →L[ℝ] Point 3)‖ + ‖(clm A₂ - clm A₁).comp (clm A₁.symm)‖ :=
            norm_add_le _ _
        _ = 1 + ‖(clm A₂ - clm A₁).comp (clm A₁.symm)‖ := by rw [norm_one]
        _ ≤ 1 + ‖clm A₂ - clm A₁‖ * ‖clm A₁.symm‖ := by gcongr
        _ ≤ 1 + δ * C := by
            have h9 : ‖clm A₂ - clm A₁‖ * ‖clm A₁.symm‖ ≤ δ * C := by
              nlinarith [hdist, h_inv1, h_symm, norm_nonneg (clm A₂ - clm A₁), norm_nonneg (clm A₁.symm)]
            linarith
        _ = α := by
            simp only [hδ_def]
            field_simp [hC.ne'] <;> ring
    exact h_goal
  -- Second direction
  have h_dir2 : ‖(clm A₁).comp (clm A₂.symm)‖ ≤ α := by
    have h_decomp : (clm A₁).comp (clm A₂.symm) =
        (clm A₂).comp (clm A₂.symm) + (clm A₁ - clm A₂).comp (clm A₂.symm) := by
      have h : clm A₁ = clm A₂ + (clm A₁ - clm A₂) := by abel
      rw [h]
      simp [ContinuousLinearMap.add_comp] <;> rfl
    have h_neg : ‖clm A₁ - clm A₂‖ = ‖clm A₂ - clm A₁‖ := by
      have h : clm A₁ - clm A₂ = -(clm A₂ - clm A₁) := by abel
      rw [h, norm_neg]
    have h_goal : ‖(clm A₁).comp (clm A₂.symm)‖ ≤ α := by
      rw [h_decomp]
      rw [hfg2]
      have h_bound : ‖(clm A₁ - clm A₂).comp (clm A₂.symm)‖ ≤
          ‖clm A₁ - clm A₂‖ * ‖clm A₂.symm‖ := ContinuousLinearMap.opNorm_comp_le _ _
      calc
        ‖(1 : Point 3 →L[ℝ] Point 3) + (clm A₁ - clm A₂).comp (clm A₂.symm)‖
          ≤ ‖(1 : Point 3 →L[ℝ] Point 3)‖ + ‖(clm A₁ - clm A₂).comp (clm A₂.symm)‖ :=
            norm_add_le _ _
        _ = 1 + ‖(clm A₁ - clm A₂).comp (clm A₂.symm)‖ := by rw [norm_one]
        _ ≤ 1 + ‖clm A₁ - clm A₂‖ * ‖clm A₂.symm‖ := by gcongr
        _ ≤ 1 + ‖clm A₂ - clm A₁‖ * ‖clm A₂.symm‖ := by rw [h_neg]
        _ ≤ 1 + δ * C := by
            have h9 : ‖clm A₂ - clm A₁‖ * ‖clm A₂.symm‖ ≤ δ * C := by
              nlinarith [hdist, h_inv2, norm_nonneg (clm A₂ - clm A₁), norm_nonneg (clm A₂.symm)]
            linarith
        _ = α := by
            simp only [hδ_def]
            field_simp [hC.ne'] <;> ring
    exact h_goal
  have h_clm_dir1 : clm (A₁.symm.trans A₂) = (clm A₂).comp (clm A₁.symm) := clm_trans A₁.symm A₂
  have h_clm_dir2 : clm (A₂.symm.trans A₁) = (clm A₁).comp (clm A₂.symm) := clm_trans A₂.symm A₁
  exact ⟨by rw [h_clm_dir1]; exact h_dir1, by rw [h_clm_dir2]; exact h_dir2⟩

/-- **General packing bound**: Given `C > 0` and `α > 1`, there exists `D : ℕ`
such that any set `S` of shapes satisfying:
1. Every `A ∈ S` is `C`-close to identity
2. Distinct elements of `S` are NOT `α`-close
has cardinality at most `D`. -/
theorem packing_bound_general {C α : ℝ} (hC : 0 < C) (hα : 1 < α) :
    ∃ (D : ℕ), ∀ (S : Set (Point 3 ≃ₗ[ℝ] Point 3)),
      (∀ A ∈ S, ShapeClose C (1 : Point 3 ≃ₗ[ℝ] Point 3) A) →
      (∀ A₁ ∈ S, ∀ A₂ ∈ S, A₁ ≠ A₂ → ¬ ShapeClose α A₁ A₂) →
      Set.Finite S ∧ S.ncard ≤ D := by
  let ε := (α - 1) / (2 * C)
  have hε_pos : 0 < ε := by positivity
  let K := boundedShapeImage C
  have hK_compact : IsCompact K := boundedShapeImage_compact (le_of_lt hC)
  have hK_tb : TotallyBounded K := hK_compact.totallyBounded
  have h_main : ∀ (ε' : ℝ), 0 < ε' →
      ∃ (t : Set (Point 3 →L[ℝ] Point 3)), t.Finite ∧ K ⊆ ⋃ y ∈ t, Metric.ball y ε' :=
    Metric.totallyBounded_iff.mp hK_tb
  rcases h_main ε hε_pos with ⟨t, ht_fin, ht_cover⟩
  let D := t.ncard
  have h_goal : ∀ (S : Set (Point 3 ≃ₗ[ℝ] Point 3)),
      (∀ A ∈ S, ShapeClose C (1 : Point 3 ≃ₗ[ℝ] Point 3) A) →
      (∀ A₁ ∈ S, ∀ A₂ ∈ S, A₁ ≠ A₂ → ¬ ShapeClose α A₁ A₂) →
      Set.Finite S ∧ S.ncard ≤ D := by
    intro S hS_bounded hS_separated
    classical
    let S_img := clm '' S
    have hS_img_sub_K : S_img ⊆ K := by
      rintro g ⟨A, hA, rfl⟩
      exact ⟨A, hS_bounded A hA, rfl⟩
    have h_choose : ∀ A ∈ S, ∃ (f : Point 3 →L[ℝ] Point 3), f ∈ t ∧ dist (clm A) f < ε := by
      intro A hA
      have hK : clm A ∈ K := hS_img_sub_K ⟨A, hA, rfl⟩
      have h : clm A ∈ ⋃ y ∈ t, Metric.ball y ε := ht_cover hK
      rcases Set.mem_iUnion₂.mp h with ⟨f, hft, hball⟩
      exact ⟨f, hft, hball⟩
    let f : (Point 3 ≃ₗ[ℝ] Point 3) → (Point 3 →L[ℝ] Point 3) := fun A =>
      if h : A ∈ S then Classical.choose (h_choose A h) else (0 : Point 3 →L[ℝ] Point 3)
    have hft : ∀ A ∈ S, f A ∈ t := by
      intro A hA
      have h5 : f A = Classical.choose (h_choose A hA) := by
        simp only [f]
        rw [dif_pos hA]
      rw [h5]
      exact (Classical.choose_spec (h_choose A hA)).1
    have hdist2 : ∀ A ∈ S, dist (clm A) (f A) < ε := by
      intro A hA
      have h5 : f A = Classical.choose (h_choose A hA) := by
        simp only [f]
        rw [dif_pos hA]
      rw [h5]
      exact (Classical.choose_spec (h_choose A hA)).2
    have h_img_sub : f '' S ⊆ t := by
      rintro g ⟨A, hA, rfl⟩
      exact hft A hA
    have h_maps_to : Set.MapsTo f S t := by
      intro A hA
      exact hft A hA
    have h_inj : Set.InjOn f S := by
      intro A1 hA1 A2 hA2 h_eq
      have h_comm : dist (f A2) (clm A2) = dist (clm A2) (f A2) := dist_comm _ _
      have h1 : dist (clm A1) (clm A2) < 2 * ε := by
        have h2 : dist (clm A1) (f A1) < ε := hdist2 A1 hA1
        have h3 : dist (clm A2) (f A2) < ε := hdist2 A2 hA2
        have h4 : f A1 = f A2 := h_eq
        rw [h4] at h2
        calc
          dist (clm A1) (clm A2)
            ≤ dist (clm A1) (f A2) + dist (f A2) (clm A2) := dist_triangle _ _ _
          _ = dist (clm A1) (f A2) + dist (clm A2) (f A2) := by rw [h_comm]
          _ < ε + ε := by linarith
          _ = 2 * ε := by ring
      have h1' : ‖clm A1 - clm A2‖ ≤ 2 * ε := by
        have h : dist (clm A1) (clm A2) = ‖clm A1 - clm A2‖ := by
          simp [dist_eq_norm]
        rw [h] at h1
        exact le_of_lt h1
      have h2ε : 2 * ε = (α - 1) / C := by
        simp only [ε]
        field_simp [hC.ne'] <;> ring
      rw [h2ε] at h1'
      have h_sc : ShapeClose α A1 A2 :=
        operatorNormClose_imp_shapeClose hα hC
          (hS_bounded A1 hA1) (hS_bounded A2 hA2) h1'
      by_cases hne : A1 = A2
      · exact hne
      · exfalso
        exact hS_separated A1 hA1 A2 hA2 hne h_sc
    have hS_finite : Set.Finite S := ht_fin.of_injOn h_maps_to h_inj
    have h_ncard : S.ncard ≤ t.ncard := by
      have h_img_fin : Set.Finite (f '' S) := ht_fin.subset h_img_sub
      have h1 : (f '' S).ncard = S.ncard := by
        exact Set.InjOn.ncard_image h_inj
      have h2 : (f '' S).ncard ≤ t.ncard := by
        exact Set.ncard_le_ncard h_img_sub ht_fin
      rw [←h1]
      exact h2
    exact ⟨hS_finite, h_ncard⟩
  exact ⟨D, h_goal⟩

/-- **Packing bound**: Given `α > 1`, there exists `D : ℕ` such that any set
`S` of shapes satisfying:
1. Every `A ∈ S` is `α^4`-close to identity
2. Distinct elements of `S` are NOT `α`-close
has cardinality at most `D`. -/
theorem packing_bound {α : ℝ} (hα : 1 < α) :
    ∃ (D : ℕ), ∀ (S : Set (Point 3 ≃ₗ[ℝ] Point 3)),
      (∀ A ∈ S, ShapeClose (α ^ 4) (1 : Point 3 ≃ₗ[ℝ] Point 3) A) →
      (∀ A₁ ∈ S, ∀ A₂ ∈ S, A₁ ≠ A₂ → ¬ ShapeClose α A₁ A₂) →
      Set.Finite S ∧ S.ncard ≤ D :=
  packing_bound_general (by positivity) hα

end Kakeya.CV.ShapeSpace
