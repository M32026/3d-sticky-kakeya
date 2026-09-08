import MyLeanRepo.Kakeya.Streamlined.DilatedTubeCover.FullContainmentFibers

/-!
# Quantitative all-scale structures with explicit tube dilation

The unit-length tube model does not admit strict containment in an undilated
coarse unit tube at every scale.  This structure records the paper's harmless
absolute enlargement convention explicitly: every fine tube is assigned to a
coarse tube whose fixed homothetic dilation contains it.

The choices at different scales are independent.  No transition map or
cross-scale coherence is included.

`DilatedUniformTubeStructure` is an internal quantitative carrier: its
`uniformity` is one finite loss for the fixed runtime scale `delta`.  By
itself it is not the paper's all-real `≈` convention.  The paper-facing
certificate is `ApproxDilatedUniformTubeStructure epsilon F`, which records
the required subpolynomial bound `uniformity ≤ delta⁻ᵉᵖˢⁱˡᵒⁿ`.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- Raw quantitative all-real-scale tube data with explicit cover dilation. -/
structure DilatedUniformTubeStructure
    {delta A : ℝ} (F : TubeFamily delta) where
  coarse :
    ∀ rho : AdmissibleScale delta, TubeFamily rho.1
  cover :
    ∀ rho : AdmissibleScale delta,
      DilatedTubeCover A F (coarse rho)
  uniformity : ENNReal
  one_le_uniformity : 1 ≤ uniformity
  uniformity_ne_top : uniformity ≠ ⊤
  uniform :
    ∀ rho, (cover rho).IsCUniform uniformity
  coarse_distinct :
    ∀ rho, (coarse rho).IsEssentiallyDistinct

/--
Paper-facing all-real `≈`-uniformity at one requested loss exponent.

The quantifier `∀ epsilon > 0` belongs to the theorem producing these
certificates as `delta → 0`; it cannot be encoded by requiring one fixed
runtime structure to satisfy every exponent simultaneously.
-/
structure ApproxDilatedUniformTubeStructure
    {delta A : ℝ} (epsilon : ℝ) (F : TubeFamily delta) extends
    DilatedUniformTubeStructure (A := A) F where
  uniformity_le :
    toDilatedUniformTubeStructure.uniformity ≤
      Kakeya.realRpowENN delta (-epsilon)

namespace ApproxDilatedUniformTubeStructure

/-- Forget the subpolynomial certificate and retain the raw all-scale data. -/
abbrev raw
    {delta A epsilon : ℝ} {F : TubeFamily delta}
    (U : ApproxDilatedUniformTubeStructure
      (A := A) epsilon F) :
    DilatedUniformTubeStructure (A := A) F :=
  U.toDilatedUniformTubeStructure

end ApproxDilatedUniformTubeStructure

/--
Internal extension carrying a uniform auxiliary parent partition.

The inherited raw structure carries the correct complete full-fiber geometry.
Assigned uniformity is additional bookkeeping and is never required by a
paper-facing `≈` certificate.
-/
structure AssignedDilatedUniformTubeStructure
    {delta A : ℝ} (F : TubeFamily delta) extends
    DilatedUniformTubeStructure (A := A) F where
  assignedUniformity : ENNReal
  one_le_assignedUniformity : 1 ≤ assignedUniformity
  assignedUniformity_ne_top : assignedUniformity ≠ ⊤
  assignedUniform :
    ∀ rho,
      (cover rho).toFactoring.FibersAreCUniform assignedUniformity
  assignedUniformity_le_uniformity :
    assignedUniformity ≤ uniformity

namespace DilatedUniformTubeStructure

/-- Every auxiliary assigned fiber is Frostman at every real scale. -/
def AssignedIsFrostmanAtEveryScale
    {delta A : ℝ} {F : TubeFamily delta}
    (U : DilatedUniformTubeStructure (A := A) F)
    (bound : ENNReal) : Prop :=
  ∀ rho : AdmissibleScale delta,
    ∀ parent : Fin (U.coarse rho).card,
      (U.cover rho).assignedFiberFrostmanConstant parent ≤ bound

/--
Every paper-semantic full geometric containment fiber is Frostman in the
fixed dilation of its coarse parent at every real scale.
-/
def IsFrostmanAtEveryScale
    {delta A : ℝ} {F : TubeFamily delta}
    (U : DilatedUniformTubeStructure (A := A) F)
    (bound : ENNReal) : Prop :=
  ∀ rho : AdmissibleScale delta,
    ∀ parent : Fin (U.coarse rho).card,
      (U.cover rho).fullContainmentFiberFrostmanConstant parent ≤ bound

/-- Every complete geometric containment fiber is branching-uniform at every
real scale. -/
def FullContainmentIsCUniformAtEveryScale
    {delta A : ℝ} {F : TubeFamily delta}
    (U : DilatedUniformTubeStructure (A := A) F)
    (bound : ENNReal) : Prop :=
  ∀ rho : AdmissibleScale delta,
    (U.cover rho).FullContainmentFibersAreCUniform bound

/-- The canonical structure field is exactly full-containment uniformity at
every real scale. -/
lemma isCUniformAtEveryScale
    {delta A : ℝ} {F : TubeFamily delta}
    (U : DilatedUniformTubeStructure (A := A) F) :
    U.FullContainmentIsCUniformAtEveryScale U.uniformity :=
  U.uniform

/-- Weaken a full-containment branching bound. -/
lemma fullContainmentIsCUniformAtEveryScale_weaken
    {delta A : ℝ} {F : TubeFamily delta}
    {U : DilatedUniformTubeStructure (A := A) F}
    {C₁ C₂ : ENNReal}
    (hC : C₁ ≤ C₂)
    (h : U.FullContainmentIsCUniformAtEveryScale C₁) :
    U.FullContainmentIsCUniformAtEveryScale C₂ := by
  intro rho
  refine ⟨(h rho).1.trans hC, ?_⟩
  intro first second
  exact (h rho).2 first second |>.trans (by gcongr)

/-- Every chosen coarse family is Katz--Tao at every real scale. -/
def IsKatzTaoAtEveryScale
    {delta A : ℝ} {F : TubeFamily delta}
    (U : DilatedUniformTubeStructure (A := A) F)
    (bound : ENNReal) : Prop :=
  ∀ rho : AdmissibleScale delta,
    (U.coarse rho).toBodyFamily.deltaMax ≤ bound

end DilatedUniformTubeStructure

namespace AssignedDilatedUniformTubeStructure

/-- Every auxiliary assigned fiber is Frostman at every real scale. -/
def AssignedIsFrostmanAtEveryScale
    {delta A : ℝ} {F : TubeFamily delta}
    (U : AssignedDilatedUniformTubeStructure (A := A) F)
    (bound : ENNReal) : Prop :=
  ∀ rho : AdmissibleScale delta,
    ∀ parent : Fin (U.coarse rho).card,
      (U.cover rho).assignedFiberFrostmanConstant parent ≤ bound

end AssignedDilatedUniformTubeStructure

end Kakeya.Streamlined

end
