import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.CoverFiberFamilies
import MyLeanRepo.Kakeya.Streamlined.UniformRefinement.SingleScaleCover
import MyLeanRepo.Kakeya.Streamlined.DilatedCoverUniformization

/-!
# Transport tube families across equal scale parameters

Some finite-grid adapters identify two real scale expressions only after
reversing a dependent `Fin` index.  The underlying tubes and covers do not
change; only the definitional scale parameter does.  This module centralizes
that harmless transport and its basic invariants.
-/

noncomputable section

open Kakeya.Streamlined

namespace Kakeya.Streamlined.RandomTranslation.WithShading

/-- Reinterpret a tube family at a propositionally equal scale. -/
def scaleTransportTubeFamily {r r' : ℝ}
    (h : r = r') (F : TubeFamily r) : TubeFamily r' := by
  subst h
  exact F

@[simp]
lemma scaleTransportTubeFamily_card {r r' : ℝ}
    (h : r = r') (F : TubeFamily r) :
    (scaleTransportTubeFamily h F).card = F.card := by
  subst h
  rfl

lemma scaleTransportTubeFamily_carrier {r r' : ℝ}
    (h : r = r') (F : TubeFamily r)
    (i : Fin (scaleTransportTubeFamily h F).card) :
    ((scaleTransportTubeFamily h F).tube i).carrier =
      (F.tube (Fin.cast (scaleTransportTubeFamily_card h F) i)).carrier := by
  subst h
  rfl

/-- Reinterpreting only the scale parameter does not change maximal density. -/
lemma scaleTransportTubeFamily_deltaMax {r r' : ℝ}
    (h : r = r') (F : TubeFamily r) :
    (scaleTransportTubeFamily h F).toBodyFamily.deltaMax =
      F.toBodyFamily.deltaMax := by
  subst h
  rfl

/-- Reinterpreting only the scale parameter preserves essential
distinctness. -/
lemma scaleTransportTubeFamily_isEssentiallyDistinct {r r' : ℝ}
    (h : r = r') (F : TubeFamily r)
    (hF : F.IsEssentiallyDistinct) :
    (scaleTransportTubeFamily h F).IsEssentiallyDistinct := by
  subst h
  exact hF

/-- Reinterpret the coarse side of a cover at an equal scale. -/
def scaleTransportTubeCover {delta r r' : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily r}
    (h : r = r') (P : TubeCover fine coarse) :
    TubeCover fine (scaleTransportTubeFamily h coarse) := by
  subst h
  exact P

@[simp]
lemma scaleTransportTubeCover_parent {delta r r' : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily r}
    (h : r = r') (P : TubeCover fine coarse)
    (i : Fin fine.card) :
    (scaleTransportTubeCover h P).parent i =
      Fin.cast (scaleTransportTubeFamily_card h coarse).symm
        (P.parent i) := by
  subst h
  rfl

lemma scaleTransportTubeCover_assignedUniform {delta r r' : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily r}
    (h : r = r') (P : TubeCover fine coarse)
    (C : ENNReal) (hP : P.toFactoring.FibersAreCUniform C) :
    (scaleTransportTubeCover h P).toFactoring.FibersAreCUniform C := by
  subst h
  exact hP

/-- Reinterpret the coarse side of a dilated cover at an equal scale. -/
def scaleTransportDilatedTubeCover
    {delta r r' A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily r}
    (h : r = r')
    (P : DilatedTubeCover A fine coarse) :
    DilatedTubeCover A fine (scaleTransportTubeFamily h coarse) := by
  subst h
  exact P

@[simp]
lemma scaleTransportDilatedTubeCover_parent
    {delta r r' A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily r}
    (h : r = r')
    (P : DilatedTubeCover A fine coarse)
    (index : Fin fine.card) :
    (scaleTransportDilatedTubeCover h P).parent index =
      Fin.cast (scaleTransportTubeFamily_card h coarse).symm
        (P.parent index) := by
  subst h
  rfl

lemma scaleTransportDilatedTubeCover_uniform
    {delta r r' A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily r}
    (h : r = r')
    (P : DilatedTubeCover A fine coarse)
    (C : ENNReal)
    (hP : P.IsCUniform C) :
    (scaleTransportDilatedTubeCover h P).IsCUniform C := by
  subst h
  exact hP

/-- Reinterpreting only the scale parameter preserves assigned-fiber
Frostman control on the actual dilated parent bodies. -/
lemma scaleTransportDilatedTubeCover_assignedFrostman
    {delta r r' A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily r}
    (h : r = r')
    (P : DilatedTubeCover A fine coarse)
    (C : ENNReal)
    (hP : P.toFactoring.FibersAreCFrostman C) :
    (scaleTransportDilatedTubeCover h P).toFactoring.FibersAreCFrostman C := by
  subst h
  exact hP

@[simp]
lemma scaleTransportDilatedTubeCover_fiberCount
    {delta r r' A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily r}
    (h : r = r')
    (P : DilatedTubeCover A fine coarse)
    (parent :
      Fin (scaleTransportTubeFamily h coarse).card) :
    (scaleTransportDilatedTubeCover h P).toFactoring.fiberCount parent =
      P.toFactoring.fiberCount
        (Fin.cast (scaleTransportTubeFamily_card h coarse) parent) := by
  subst h
  rfl

end Kakeya.Streamlined.RandomTranslation.WithShading

end
