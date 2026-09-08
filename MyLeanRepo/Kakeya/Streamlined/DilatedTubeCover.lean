import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeContainment

/-!
# Paper-facing single-scale dilated tube covers

This leaf module contains the geometric cover data used by the GWZ
full-containment semantics.  It deliberately has no dependency on the
historical strict assigned-cover refinement implementation.
-/

noncomputable section

namespace Kakeya.Streamlined

/--
The carrier of a tube after homothetic dilation about the midpoint of its
defining unit segment.
-/
def dilatedTubeCarrier {ρ : ℝ} (A : ℝ) (T : Kakeya.DeltaTube ρ) :
    Set Point3 :=
  let midpoint := T.base + (1 / 2 : ℝ) • T.direction
  AffineMap.homothety midpoint A '' T.carrier

/--
A parent assignment in which each fine tube is contained in a fixed
homothetic dilation of its assigned coarse tube.
-/
structure DilatedTubeCover {δ ρ : ℝ} (A : ℝ)
    (fine : TubeFamily δ) (coarse : TubeFamily ρ) where
  parent : Fin fine.card → Fin coarse.card
  parent_surjective : Function.Surjective parent
  nested :
    ∀ i, (fine.tube i).carrier ⊆
      dilatedTubeCarrier A (coarse.tube (parent i))

/-- One coarse tube represented by its actual dilated carrier. -/
def dilatedTubeBody
    {rho : ℝ} (A : ℝ) (tube : Kakeya.DeltaTube rho) : Body :=
  ⟨dilatedTubeCarrier A tube⟩

/-- A coarse tube family represented by its actual dilated carriers. -/
def dilatedTubeBodyFamily
    {rho : ℝ} (A : ℝ) (coarse : TubeFamily rho) : BodyFamily where
  card := coarse.card
  body j := dilatedTubeBody A (coarse.tube j)

namespace DilatedTubeCover

/--
Convert a dilated tube cover to the authoritative partition structure on the
actual dilated parent bodies.

This is the only valid factoring conversion for a general dilated cover:
containment need not hold in the undilated coarse unit tubes.
-/
def toFactoring
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (cover : DilatedTubeCover A fine coarse) :
    Factoring fine.toBodyFamily (dilatedTubeBodyFamily A coarse) where
  parent := cover.parent
  parent_surjective := cover.parent_surjective
  contained := cover.nested

@[simp]
lemma toFactoring_parent
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (cover : DilatedTubeCover A fine coarse)
    (i : Fin fine.card) :
    cover.toFactoring.parent i = cover.parent i :=
  rfl

@[simp]
lemma toFactoring_fiberIndices
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (cover : DilatedTubeCover A fine coarse)
    (j : Fin coarse.card) :
    cover.toFactoring.fiberIndices j =
      Finset.univ.filter fun i : Fin fine.card =>
        cover.parent i = j :=
  rfl

end DilatedTubeCover

/--
A dilated cover that preserves the scale-local coaxial-line geometry.

Axial midpoint displacement is intentionally unrestricted: the paper's tube
metric compares coaxial lines and directions, not the chosen endpoints of two
unit segments.  The transverse midpoint component and the direction up to
orientation are controlled at scale `rho`.
-/
structure LocalDilatedTubeCover {δ ρ : ℝ} (A C : ℝ)
    (fine : TubeFamily δ) (coarse : TubeFamily ρ) extends
    DilatedTubeCover A fine coarse where
  transverse_midpoint_close :
    ∀ i,
      ‖(GeometricLemmas.tubeMidpoint (fine.tube i) -
          GeometricLemmas.tubeMidpoint (coarse.tube (parent i))) -
        inner ℝ
          (GeometricLemmas.tubeMidpoint (fine.tube i) -
            GeometricLemmas.tubeMidpoint (coarse.tube (parent i)))
          (coarse.tube (parent i)).direction •
            (coarse.tube (parent i)).direction‖ ≤ C * ρ
  direction_close_or_reverse :
    ∀ i,
      ‖(fine.tube i).direction -
          (coarse.tube (parent i)).direction‖ ≤ C * ρ ∨
        ‖(fine.tube i).direction +
          (coarse.tube (parent i)).direction‖ ≤ C * ρ

/--
At one scale, every essentially-distinct fine family has a cover by an
essentially-distinct coarse family after one universal homothetic dilation.

The dilation makes explicit the paper's harmless absolute-constant
enlargement convention for tubes.  Requiring strict containment in an
undilated unit-length coarse tube is false because of axial endpoint effects.
-/
def SingleScaleTubeCoverStatement : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧
    ∀ δ ρ : ℝ, 0 < δ → δ ≤ ρ → ρ ≤ 1 →
      ∀ F : TubeFamily δ,
        F.Nonempty →
        F.IsInUnitBall →
        F.IsEssentiallyDistinct →
        ∃ coarse : TubeFamily ρ,
          ∃ cover : DilatedTubeCover A F coarse,
            coarse.IsEssentiallyDistinct

end Kakeya.Streamlined
