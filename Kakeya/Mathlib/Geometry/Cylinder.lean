/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Cylinders along a direction in an inner product space

Dimension-free, project-type-free API for the set `cylinder m d a b r`: the points `p`
whose component along `d` (measured as `inner (p - m) d`) lies in `[a, b]` and whose
component orthogonal to `d` has norm at most `r`. We record that it is closed, behaves
well under translation, and (for a unit direction `d`) compute its volume as the product
of the axial length `b - a` with the volume of a radius-`r` ball in the orthogonal
complement `(ℝ ∙ d)ᗮ`.
-/

open MeasureTheory ENNReal

@[expose] public section

section Cylinder

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Cylinder of half-length-style range `[a, b]` along a (unit) direction `d`,
centred so that `inner (p - m) d ∈ Icc a b` and the component of `p - m`
orthogonal to `d` has norm at most `r`. When `‖d‖ = 1`, the parameter `r` is
literally the cross-section radius; for non-unit `d` the definition is still
well-typed but not geometrically natural. -/
def cylinder (m d : E) (a b r : ℝ) : Set E :=
  {p | inner ℝ (p - m) d ∈ Set.Icc a b ∧
       ‖(p - m) - (inner ℝ (p - m) d : ℝ) • d‖ ≤ r}

lemma mem_cylinder {m d : E} {a b r : ℝ} {p : E} :
    p ∈ cylinder m d a b r ↔
      inner ℝ (p - m) d ∈ Set.Icc a b ∧
      ‖(p - m) - (inner ℝ (p - m) d : ℝ) • d‖ ≤ r := Iff.rfl

/-- The cylinder is closed (in any normed inner product space). -/
lemma isClosed_cylinder (m d : E) (a b r : ℝ) :
    IsClosed (cylinder m d a b r) := by
  have hf₁ : Continuous (fun p : E => (inner ℝ (p - m) d : ℝ)) := by
    exact (continuous_id.sub continuous_const).inner continuous_const
  have hf₂ : Continuous
      (fun p : E => ‖(p - m) - (inner ℝ (p - m) d : ℝ) • d‖) := by
    refine Continuous.norm ?_
    exact (continuous_id.sub continuous_const).sub (hf₁.smul continuous_const)
  have h1 : IsClosed {p : E | (inner ℝ (p - m) d : ℝ) ∈ Set.Icc a b} :=
    isClosed_Icc.preimage hf₁
  have h2 : IsClosed
      {p : E | ‖(p - m) - (inner ℝ (p - m) d : ℝ) • d‖ ≤ r} :=
    isClosed_Iic.preimage hf₂
  exact h1.inter h2

/-- Translating the centre by `v` translates the cylinder by `v`. -/
lemma cylinder_vadd (m d : E) (a b r : ℝ) (v : E) :
    cylinder (m + v) d a b r = (fun p => p + v) '' cylinder m d a b r := by
  ext p
  simp only [cylinder, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨p - v, ⟨?_, ?_⟩, by abel⟩
    · have heq : p - v - m = p - (m + v) := by abel
      rw [heq]; exact h1
    · have heq : p - v - m = p - (m + v) := by abel
      rw [heq]; exact h2
  · rintro ⟨q, ⟨h1, h2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have heq : q + v - (m + v) = q - m := by abel
      rw [heq]; exact h1
    · have heq : q + v - (m + v) = q - m := by abel
      rw [heq]; exact h2

end Cylinder

section VolumeCylinder

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Volume of a cylinder centred at the origin along a unit direction `d`,
spanning `Icc a b` in the `d`-direction with cross-section radius `r`. -/
lemma volume_cylinder_zero {d : E} (hd : ‖d‖ = 1) (a b r : ℝ) :
    volume (cylinder (0 : E) d a b r) =
      ENNReal.ofReal (b - a) *
        volume (Metric.closedBall (0 : ((ℝ ∙ d)ᗮ : Submodule ℝ E)) r) := by
  set K : Submodule ℝ E := ℝ ∙ d with hK_def
  -- The map f : E → ℝ × Kᗮ sending p ↦ (⟨d, p⟩, p - ⟨d, p⟩ • d) is a
  -- composition of measure-preserving maps:
  --   E ≃ₗᵢ[ℝ] WithLp 2 (K × Kᗮ) ≃ᵐ (K × Kᗮ) ≃ᵐ ℝ × Kᗮ
  let φ : ℝ ≃ₗᵢ[ℝ] K := LinearIsometryEquiv.toSpanUnitSingleton d hd
  -- The composed linear isometry e₁ : E ≃ₗᵢ WithLp 2 (ℝ × Kᗮ)
  let e₁ : E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × (Kᗮ : Submodule ℝ E)) :=
    K.orthogonalDecomposition.trans
      (LinearIsometryEquiv.withLpProdCongr 2 φ.symm
        (LinearIsometryEquiv.refl ℝ (Kᗮ : Submodule ℝ E)))
  -- The full map: compose with WithLp.ofLp.
  let f : E → ℝ × (Kᗮ : Submodule ℝ E) :=
    fun p => WithLp.ofLp (e₁ p)
  -- Step 1: f is measure preserving.
  have hf_mp : MeasurePreserving f := by
    have h₁ : MeasurePreserving (e₁ : E → WithLp 2 (ℝ × (Kᗮ : Submodule ℝ E))) :=
      e₁.measurePreserving
    have h₂ : MeasurePreserving (@WithLp.ofLp 2 (ℝ × (Kᗮ : Submodule ℝ E))) :=
      WithLp.volume_preserving_ofLp ℝ (Kᗮ : Submodule ℝ E)
    exact h₂.comp h₁
  -- Step 2: cylinder is the preimage of `Icc a b ×ˢ closedBall 0 r` under f.
  have h_eq : cylinder (0 : E) d a b r =
      f ⁻¹' (Set.Icc a b ×ˢ Metric.closedBall (0 : (Kᗮ : Submodule ℝ E)) r) := by
    ext p
    simp only [cylinder, sub_zero, Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_prod, Metric.mem_closedBall, dist_zero_right]
    -- Compute f p explicitly.
    have hfp_e₁ : e₁ p =
        WithLp.toLp 2 (φ.symm (K.orthogonalProjectionOnto p),
          (Kᗮ.orthogonalProjectionOnto p : Kᗮ)) := by
      change LinearIsometryEquiv.withLpProdCongr 2 φ.symm
              (LinearIsometryEquiv.refl ℝ (Kᗮ : Submodule ℝ E))
              (K.orthogonalDecomposition p) = _
      rw [Submodule.orthogonalDecomposition_apply]
      simp [LinearIsometryEquiv.withLpProdCongr]
    have hK_proj : K.orthogonalProjectionOnto p = φ (inner ℝ p d) := by
      apply Subtype.ext
      change K.starProjection p = (inner ℝ p d : ℝ) • d
      rw [Submodule.starProjection_unit_singleton (𝕜 := ℝ) hd, real_inner_comm]
    have hfp_fst : (f p).1 = inner ℝ p d := by
      change (e₁ p).ofLp.1 = inner ℝ p d
      rw [hfp_e₁]
      change φ.symm (K.orthogonalProjectionOnto p) = inner ℝ p d
      rw [hK_proj, LinearIsometryEquiv.symm_apply_apply]
    have hfp_snd_norm : ‖(f p).2‖ = ‖p - (inner ℝ p d : ℝ) • d‖ := by
      change ‖(e₁ p).ofLp.2‖ = _
      rw [hfp_e₁]
      change ‖(Kᗮ.orthogonalProjectionOnto p : Kᗮ)‖ = _
      -- ‖u‖ in Kᗮ equals ‖↑u‖ in E
      rw [show ‖(Kᗮ.orthogonalProjectionOnto p : Kᗮ)‖ =
            ‖((Kᗮ.orthogonalProjectionOnto p : Kᗮ) : E)‖ from rfl,
        Submodule.coe_orthogonalProjectionOnto_apply,
        Submodule.starProjection_orthogonal_val,
        Submodule.starProjection_unit_singleton (𝕜 := ℝ) hd,
        real_inner_comm]
    rw [hfp_fst, hfp_snd_norm]
  -- Step 3: measurable set.
  have h_meas : MeasurableSet ((Set.Icc a b : Set ℝ) ×ˢ
      Metric.closedBall (0 : (Kᗮ : Submodule ℝ E)) r) :=
    measurableSet_Icc.prod measurableSet_closedBall
  -- Step 4: compute.
  rw [h_eq, hf_mp.measure_preimage h_meas.nullMeasurableSet,
    MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
    Real.volume_Icc]

/-- Volume of a cylinder centred at an arbitrary `m`, along a unit direction `d`,
spanning `Icc a b` in the `d`-direction with cross-section radius `r`. -/
lemma volume_cylinder {d : E} (hd : ‖d‖ = 1) (m : E) (a b r : ℝ) :
    volume (cylinder m d a b r) =
      ENNReal.ofReal (b - a) *
        volume (Metric.closedBall (0 : ((ℝ ∙ d)ᗮ : Submodule ℝ E)) r) := by
  have h_set : cylinder m d a b r = (fun p => p + m) '' cylinder 0 d a b r := by
    have h := cylinder_vadd (0 : E) d a b r m
    simpa using h
  rw [h_set, Set.image_add_right, measure_preimage_add_right,
    volume_cylinder_zero hd]

end VolumeCylinder
