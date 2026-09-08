module

/-
Source-faithful definitions for Wang--Zahl, Definition 1.5.

Source: blueprint/src/WZ2/250224e_K3.tex, lines 198--275 in the current
repository version (label defnCDE).
-/

public import Kakeya.PartialEstimates
public import Kakeya.Mathlib.Analysis.AffineSubspace

@[expose] public section

open MeasureTheory

namespace Kakeya.WangZahl

noncomputable section

universe u

/-- The ambient space in Wang--Zahl Definition 1.5. -/
abbrev Space3 := EuclideanSpace ℝ (Fin 3)

/-- A convex test set in `R^3`.

Unlike `ConvexSpaceBody`, the source does not require the test set to be
nonempty, compact, or bounded. -/
structure ConvexTestSet where
  carrier : Set Space3
  convex_carrier : Convex ℝ carrier

/-- A hyperplane in `R^3`, represented as an affine subspace of affine
dimension two. -/
structure Hyperplane3 where
  carrier : AffineSubspace ℝ Space3
  nonempty_carrier : (carrier : Set Space3).Nonempty
  finrank_direction : Module.finrank ℝ carrier.direction = 2

/-- A slab in the sense immediately preceding Wang--Zahl Definition 1.5:
the intersection of the unit ball with a closed thickened neighbourhood of a
hyperplane. -/
structure SlabTestSet where
  plane : Hyperplane3
  thickness : NNReal

/-- The underlying subset of a Wang--Zahl slab. -/
def SlabTestSet.carrier (W : SlabTestSet) : Set Space3 :=
  Metric.closedBall 0 1 ∩ Metric.cthickening (W.thickness : ℝ) W.plane.carrier

/-- A fixed model `delta`-tube, used only to give literal meaning to the
common tube volume `|T|` in Definition 1.5. -/
def modelTube (δ : NNReal) : Tube δ Space3 :=
  Tube.mk' δ (x := 0) (y := EuclideanSpace.single 0 (1 : ℝ)) (by
    rw [dist_zero_left, PiLp.norm_single, norm_one])

/-- The common volume `|T|` of a `delta`-tube in `R^3`. -/
def tubeVolume (δ : NNReal) : ENNReal := volume (modelTube δ).carrier

/-- The canonical Katz--Tao convex Wolff constant from the definition
immediately preceding Wang--Zahl Definition 1.5.

It is the infimum over positive `C` for which the stated counting estimate
holds for every convex subset of `R^3`. -/
noncomputable def katzTaoConvexWolffConstant {δ : NNReal} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) : ENNReal :=
  @sInf ENNReal _
    {C : ENNReal | 0 < C ∧ ∀ W : ConvexTestSet,
      ((@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
        (Classical.decPred _) s).card : ENNReal) ≤
        C * volume W.carrier * (tubeVolume δ)⁻¹}

/-- The canonical Frostman slab Wolff constant from the definition
immediately preceding Wang--Zahl Definition 1.5.

It is the infimum over positive `C` for which the stated counting estimate
holds for every slab. -/
noncomputable def frostmanSlabWolffConstant {δ : NNReal} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) : ENNReal :=
  @sInf ENNReal _
    {C : ENNReal | 0 < C ∧ ∀ W : SlabTestSet,
      ((@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
        (Classical.decPred _) s).card : ENNReal) ≤
        C * volume W.carrier * (s.card : ENNReal)}

/-- The source convention `(T,Y)_delta`: a finite family of essentially
distinct shaded `delta`-tubes, all contained in the unit ball. Measurability of
each shading and the inclusion `Y(T) subset T` are bundled in `ShadedTube`. -/
def IsTubeShadingFamily {δ : NNReal} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) : Prop :=
  (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) ∧
    (s : Set ι).Pairwise fun i j =>
      IsEssentiallyDistinct (T i).carrier (T j).carrier

/-- The source's `lambda`-density condition for `(T,Y)_delta`. -/
def IsDense {δ : NNReal} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) (density : NNReal) : Prop :=
  (density : ENNReal) * ∑ i ∈ s, volume (T i).carrier ≤
    ∑ i ∈ s, volume (T i).shade

/-- Wang--Zahl Definition 1.5, Assertion `D(sigma, omega)`.

The source quantifies over every positive scale `delta`, not merely all
sufficiently small scales. -/
def AssertionD (σ ω : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ κ : NNReal, ∃ η : ℝ, 0 < κ ∧ 0 < η ∧
    ∀ (δ : NNReal), 0 < δ →
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        IsTubeShadingFamily s T →
        IsDense s T ⟨(δ : ℝ) ^ η, Real.rpow_nonneg δ.coe_nonneg η⟩ →
        katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
        frostmanSlabWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
        (κ : ENNReal) * (δ : ENNReal) ^ (ω + ε) * (s.card : ENNReal) * tubeVolume δ *
              (((s.card : ENNReal) * (tubeVolume δ) ^ (1 / 2 : ℝ)) ^ (-σ)) ≤
          volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)

/-- Wang--Zahl Definition 1.5, Assertion `E(sigma, omega)`.

Here `m` and `ell` are the actual infimal constants of the input family, as in
the source; they are not upper-bound parameters. -/
def AssertionE (σ ω : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ κ : NNReal, ∃ η : ℝ, 0 < κ ∧ 0 < η ∧
    ∀ (δ : NNReal), 0 < δ →
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        IsTubeShadingFamily s T →
        IsDense s T ⟨(δ : ℝ) ^ η, Real.rpow_nonneg δ.coe_nonneg η⟩ →
        let m := katzTaoConvexWolffConstant s T
        let ell := frostmanSlabWolffConstant s T
        (κ : ENNReal) * (δ : ENNReal) ^ (ω + ε) * m ^ (-1 : ℝ) *
              (s.card : ENNReal) * tubeVolume δ *
              ((m ^ (-3 / 2 : ℝ) * ell * (s.card : ENNReal) *
                (tubeVolume δ) ^ (1 / 2 : ℝ)) ^ (-σ)) ≤
          volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)

end

end Kakeya.WangZahl
