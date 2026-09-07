module

/-
Shared definitions for the discretised Furstenberg estimate project. Extracted
from `discretised_furstenberg_estimate.lean` to break an import cycle: downstream
modules can import this Base module without pulling in the target theorem.

Contains:
- Dyadic scale, cube, and covering number definitions
- Appendix dual line / dyadic tube machinery
- Product-like incidence set and delta-SC-set definitions
- `IsDeltaSSet` definition
- `EuclideanPlane`, `AffineLine`, and its `MetricSpace` instance
- `parameterRange`
-/
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

/-- The dyadic scales used by OS Proposition A.7. -/
def dyadicScales : Set ℝ :=
  {δ | ∃ n : ℕ, δ = (2 : ℝ) ^ (-(n : ℤ))}

def dyadicCube {d : ℕ} (δ : ℝ) (k : Fin d → ℤ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i : Fin d, x i ∈ Set.Ico (δ * (k i : ℝ)) (δ * ((k i : ℝ) + 1))}

def dyadicCubes (d : ℕ) (δ : ℝ) : Set (Set (EuclideanSpace ℝ (Fin d))) :=
  {p | ∃ k : Fin d → ℤ, p = dyadicCube (d := d) δ k}

def dyadicCubesMeeting {d : ℕ} (δ : ℝ) (A : Set (EuclideanSpace ℝ (Fin d))) :
    Set (Set (EuclideanSpace ℝ (Fin d))) :=
  {p | p ∈ dyadicCubes d δ ∧ (p ∩ A).Nonempty}

def dyadicCoveringNumber {d : ℕ} (δ : ℝ) (A : Set (EuclideanSpace ℝ (Fin d))) : ℕ∞ :=
  (dyadicCubesMeeting (d := d) δ A).encard

def appendixDualLine (a b : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | p 0 = a * p 1 + b}

def appendixDualLineMap (p : EuclideanSpace ℝ (Fin 2)) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  appendixDualLine (p 0) (p 1)

def appendixDualOfParameterSet (P : Set (EuclideanSpace ℝ (Fin 2))) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {q | ∃ p ∈ P, q ∈ appendixDualLineMap p}

def appendixParameterStrip : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | p 0 ∈ Set.Icc (-1 : ℝ) 1}

def appendixDyadicTubes (δ : ℝ) : Set (Set (EuclideanSpace ℝ (Fin 2))) :=
  appendixDualOfParameterSet '' dyadicCubesMeeting (d := 2) δ appendixParameterStrip

def IsDeltaSCSet {d : ℕ} (δ s C : ℝ) (P : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  Bornology.IsBounded P ∧
    P.Nonempty ∧
      1 ≤ d ∧
        δ ∈ dyadicScales ∧
          0 < δ ∧
            0 ≤ s ∧
              s ≤ (d : ℝ) ∧
                0 < C ∧
                  ∀ ⦃r : ℝ⦄ ⦃Q : Set (EuclideanSpace ℝ (Fin d))⦄,
                    r ∈ dyadicScales →
                      Q ∈ dyadicCubes d r →
                        δ ≤ r →
                          r ≤ 1 →
                            ENat.toENNReal (dyadicCoveringNumber (d := d) δ (P ∩ Q)) ≤
                              ENNReal.ofReal C *
                                ENat.toENNReal (dyadicCoveringNumber (d := d) δ P) *
                                  ENNReal.ofReal (r ^ s)

def productLikeIntegerGrid (δ : ℝ) : Set ℝ :=
  {x | ∃ k : ℤ, x = δ * (k : ℝ)}

def productLikeUnitGrid (δ : ℝ) : Set ℝ :=
  productLikeIntegerGrid δ ∩ Set.Icc (0 : ℝ) 1

abbrev productLikeRealLineCopy (A : Set ℝ) : Set (EuclideanSpace ℝ (Fin 1)) :=
  {x | x 0 ∈ A}

abbrev IsProductLikeRealDeltaSCSet (δ s C : ℝ) (A : Set ℝ) : Prop :=
  IsDeltaSCSet (d := 1) δ s C (productLikeRealLineCopy A)

def productLikeIncidenceSet (Y : Set ℝ) (X : ℝ → Set ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ y ∈ Y, {z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ X y ∧ z 1 = y}

def productLikeAppendixDyadicTubeCanonicalParameterCube (δ : ℝ)
    (T : Set (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 2)) :=
  letI : Decidable (T ∈ appendixDyadicTubes δ) := Classical.propDecidable _
  if hT : T ∈ appendixDyadicTubes δ then Classical.choose hT else ∅

def productLikeAppendixDyadicTubeParameterSet (δ : ℝ)
    (𝒯 : Set (Set (EuclideanSpace ℝ (Fin 2)))) : Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃₀ (productLikeAppendixDyadicTubeCanonicalParameterCube δ '' 𝒯)

def IsProductLikeAppendixDeltaSCSetOfDyadicTubes (δ s C : ℝ)
    (𝒯 : Set (Set (EuclideanSpace ℝ (Fin 2)))) : Prop :=
  𝒯 ⊆ appendixDyadicTubes δ ∧
    0 ≤ s ∧
      s ≤ 1 ∧
        IsDeltaSCSet (d := 2) δ s C (productLikeAppendixDyadicTubeParameterSet δ 𝒯)

/--
[def.delta_s_set.440] A subset `P` of a metric space is a `(δ, s, C)`-set if, for every
center `x` and every radius `r ≥ δ`, the external covering number of `P ∩ B(x,r)` is bounded by
`C * r^s * |P|_δ`, where `B(x,r)` is the closed ball and `|P|_δ` is the external covering
number.
-/
def IsDeltaSSet {X : Type*} [PseudoMetricSpace X] (δ s C : ℝ) (P : Set X) : Prop :=
  P.Nonempty ∧ 0 < δ ∧ 0 < C ∧ 0 ≤ s ∧
    ∀ x : X, ∀ r : ℝ, δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ℝ≥0∞) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal P : ℝ≥0∞)

namespace DirecretisedFurstenbergEstimate

abbrev EuclideanPlane : Type := EuclideanSpace ℝ (Fin 2)

/--
[def.delta_sets_lines_tubes.454] The affine line space `𝓐(2,1)`: nonempty affine
subspaces of `ℝ²` whose direction has real dimension `1`.
-/
abbrev AffineLine : Type :=
  { ℓ : AffineSubspace ℝ EuclideanPlane // Module.finrank ℝ ℓ.direction = 1 }

lemma AffineLine.nonempty (ℓ : AffineLine) : (ℓ.1 : Set EuclideanPlane).Nonempty := by
  rw [AffineSubspace.nonempty_iff_ne_bot]
  by_contra! h
  have hd := ℓ.2
  rw [h, AffineSubspace.direction_bot] at hd
  simp at hd

instance (ℓ : AffineLine) : Nonempty ℓ.1 := ℓ.nonempty.to_subtype

def AffineLine.offset (ℓ : AffineLine) : EuclideanPlane :=
  EuclideanGeometry.orthogonalProjection ℓ.1 0

lemma AffineLine.offset_mem (ℓ : AffineLine) : ℓ.offset ∈ ℓ.1 :=
  (EuclideanGeometry.orthogonalProjection ℓ.1 0).2

def AffineLine.dist (ℓ₁ ℓ₂ : AffineLine) : ℝ :=
  ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ + ‖ℓ₁.offset - ℓ₂.offset‖

instance : MetricSpace AffineLine where
  dist := AffineLine.dist
  dist_self _ := by simp [AffineLine.dist]
  dist_comm _ _ := by simp [AffineLine.dist, norm_sub_rev]
  dist_triangle ℓ₁ ℓ₂ ℓ₃ := by
    unfold AffineLine.dist
    grw [norm_sub_le_norm_sub_add_norm_sub _ ℓ₂.1.direction.starProjection _,
      norm_sub_le_norm_sub_add_norm_sub _ ℓ₂.offset _]
    linarith
  eq_of_dist_eq_zero := by
    intro ℓ₁ ℓ₂ h
    unfold AffineLine.dist at h
    let dd := ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection
    let od := ℓ₁.offset - ℓ₂.offset
    have hds : ℓ₁.1.direction.starProjection = ℓ₂.1.direction.starProjection := eq_of_norm_sub_eq_zero
      (by linarith [norm_nonneg dd, norm_nonneg od])
    have ho : ℓ₁.offset = ℓ₂.offset := eq_of_norm_sub_eq_zero
      (by linarith [norm_nonneg dd, norm_nonneg od])
    have hd : ℓ₁.1.direction = ℓ₂.1.direction := by simpa using congr((·.range) $hds)
    apply Subtype.ext
    rw [AffineSubspace.eq_iff_direction_eq_of_mem ℓ₁.offset_mem (ho ▸ ℓ₂.offset_mem)]
    exact hd

/-- Typeclass for line types that can be represented in the standard
    y = m*x + b chart with bounded slope |m| ≤ 1.

    Unlike `HasSlope`, this is honest: lines not in the standard chart
    (e.g. vertical lines) are excluded by `inChart`, rather than being
    assigned a bogus slope of 0. -/
class InStandardChart (Line : Type*) where
  inChart : Line → Prop
  slope : (l : Line) → inChart l → ℝ
  intercept : (l : Line) → inChart l → ℝ
  lineOfSlopeIntercept : ℝ → ℝ → Line
  line_eq : ∀ l h, lineOfSlopeIntercept (slope l h) (intercept l h) = l

/-- Construct an AffineLine for y = m*x + b. -/
noncomputable def AffineLine.mkSlopeIntercept (m b : ℝ) : AffineLine :=
  let p : EuclideanPlane := WithLp.toLp 2 ![0, b]
  let v : EuclideanPlane := WithLp.toLp 2 ![1, m]
  let dir : Submodule ℝ EuclideanPlane := Submodule.span ℝ {v}
  let aff : AffineSubspace ℝ EuclideanPlane := AffineSubspace.mk' p dir
  have h_v_ne_zero : v ≠ 0 := by
    intro h
    have h1 : v 0 = 0 := by rw [h] <;> simp
    have h2 : v 0 = 1 := by simp [v] <;> norm_num
    rw [h2] at h1 <;> norm_num at h1
  have h_finrank : Module.finrank ℝ dir = 1 :=
    finrank_span_singleton h_v_ne_zero
  have h_dir_eq : aff.direction = dir := AffineSubspace.direction_mk' p dir
  ⟨aff, by rw [h_dir_eq]; exact h_finrank⟩

/-- InStandardChart instance for AffineLine.

    `inChart ℓ` holds iff ℓ can be written as y = m*x + b with |m| ≤ 1. -/
noncomputable instance : InStandardChart AffineLine where
  inChart ℓ := ∃ (m b : ℝ), |m| ≤ 1 ∧ AffineLine.mkSlopeIntercept m b = ℓ
  slope ℓ h := Classical.choose h
  intercept ℓ h := Classical.choose (Classical.choose_spec h)
  lineOfSlopeIntercept := AffineLine.mkSlopeIntercept
  line_eq ℓ h :=
    (Classical.choose_spec (Classical.choose_spec h)).2

/--
[thm.discretised_furstenberg_estimate.467] The parameter range
`{(s,t) : s ∈ (0,1), t ∈ (s,2)}` for the discretised Furstenberg estimate.
-/
def parameterRange : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ p.2 ∈ Set.Ioo p.1 2}

end DirecretisedFurstenbergEstimate

end
