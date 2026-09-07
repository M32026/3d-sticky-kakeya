import MyLeanRepo.Kakeya.Cinematic.Definitions
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Geometric objects in the PYZ cinematic proof

This file contains shared definitions for the medium-sized proof targets from
Sections 3 and 4 of the paper. It contains no theorem placeholders.
-/

noncomputable section

open Set

namespace Kakeya.Cinematic

/-- Vertical translation of a cinematic function by a real constant. -/
noncomputable def C2Function.verticalTranslate (f : C2Function) (c : ℝ) :
    C2Function where
  value := f.value + ContinuousMap.const UnitPoint c
  firstDeriv := f.firstDeriv
  secondDeriv := f.secondDeriv
  hasExtension := by
    refine ⟨fun x => f.extension x + c, f.extension_contDiff.add contDiff_const,
      ?_, ?_, ?_⟩
    · intro x
      simp [C2Function.extension_eq_value]
    · intro x
      rw [deriv_add_const]
      exact f.deriv_extension_eq_firstDeriv x
    · intro x
      have hderiv :
          deriv (fun y => f.extension y + c) = deriv f.extension := by
        funext y
        exact deriv_add_const c
      rw [hderiv]
      exact f.secondDeriv_extension_eq_secondDeriv x

/-- A closed subinterval of the normalized parameter interval. -/
structure ParameterInterval where
  left : ℝ
  right : ℝ
  left_mem : left ∈ unitInterval
  right_mem : right ∈ unitInterval
  left_le_right : left ≤ right

namespace ParameterInterval

def carrier (I : ParameterInterval) : Set UnitPoint :=
  {x | I.left ≤ (x : ℝ) ∧ (x : ℝ) ≤ I.right}

def length (I : ParameterInterval) : ℝ :=
  I.right - I.left

theorem length_nonneg (I : ParameterInterval) : 0 ≤ I.length :=
  sub_nonneg.mpr I.left_le_right

def midpoint (I : ParameterInterval) : ℝ :=
  (I.left + I.right) / 2

/--
The centered interval with length factor `q`, clipped only by the ambient
parameter domain `[0,1]`.

For `0 ≤ q ≤ 1` this lies inside `I.carrier`. For `q > 1` it is the genuine
centered dilation used in PYZ Lemma 18.
-/
def centeredCarrier (I : ParameterInterval) (q : ℝ) : Set UnitPoint :=
  {x | |(x : ℝ) - I.midpoint| ≤ q * I.length / 2}

/-- The real-coordinate version of `centeredCarrier`. -/
def realCenteredCarrier (I : ParameterInterval) (q : ℝ) : Set ℝ :=
  {x | x ∈ unitInterval ∧ |x - I.midpoint| ≤ q * I.length / 2}

theorem mem_realCenteredCarrier_iff (I : ParameterInterval) (q x : ℝ) :
    x ∈ I.realCenteredCarrier q ↔
      ∃ hx : x ∈ unitInterval,
        (⟨x, hx⟩ : UnitPoint) ∈ I.centeredCarrier q := by
  constructor
  · intro hx
    exact ⟨hx.1, hx.2⟩
  · rintro ⟨hx, hcentered⟩
    exact ⟨hx, hcentered⟩

/-- A centered contraction lies in the original interval. -/
theorem centeredCarrier_subset_carrier (I : ParameterInterval) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    I.centeredCarrier q ⊆ I.carrier := by
  intro x hx
  have hlen : 0 ≤ I.length := I.length_nonneg
  have hscale : q * I.length / 2 ≤ I.length / 2 := by
    have hmul : q * I.length ≤ 1 * I.length :=
      mul_le_mul_of_nonneg_right hq1 hlen
    linarith
  have hbound :
      |(x : ℝ) - I.midpoint| ≤ I.length / 2 :=
    hx.trans hscale
  have habs := abs_le.mp hbound
  simp only [carrier, Set.mem_setOf_eq, midpoint, length]
  dsimp only [midpoint, length] at habs
  constructor <;> linarith

/-- Unit centered scaling recovers the original interval. -/
theorem centeredCarrier_one (I : ParameterInterval) :
    I.centeredCarrier 1 = I.carrier := by
  apply Set.Subset.antisymm
  · exact I.centeredCarrier_subset_carrier (by norm_num) (by norm_num)
  · intro x hx
    have hleft : I.left ≤ (x : ℝ) := hx.1
    have hright : (x : ℝ) ≤ I.right := hx.2
    rw [centeredCarrier, Set.mem_setOf_eq]
    rw [abs_le]
    simp only [midpoint, length]
    constructor <;> linarith

/-- The short-interval hypothesis used in PYZ Lemmas 13 and 14. -/
def IsShort (I : ParameterInterval) (K : ℝ) : Prop :=
  I.length ≤ (6 * K)⁻¹

/--
A subdivision interval of fixed size depending only on `K`. The lower bound
encodes the paper's use of `|J| ∼ 1` after the short-interval reduction.
-/
def IsControlled (I : ParameterInterval) (K : ℝ) : Prop :=
  (12 * K)⁻¹ ≤ I.length ∧ I.IsShort K

end ParameterInterval

/-- A finite indexed collection of parameter intervals, allowing zero pieces. -/
structure IntervalFamily where
  card : ℕ
  interval : Fin card → ParameterInterval

namespace IntervalFamily

def union (F : IntervalFamily) : Set UnitPoint :=
  {x | ∃ i : Fin F.card, x ∈ (F.interval i).carrier}

def AllLengthsLE (F : IntervalFamily) (bound : ℝ) : Prop :=
  ∀ i, (F.interval i).length ≤ bound

end IntervalFamily

/-- The centered subinterval occupying the fraction `q` of `[0,1]`. -/
def centeredSubinterval (q : ℝ) : Set UnitPoint :=
  {x | |(x : ℝ) - 1 / 2| ≤ q / 2}

def centralHalf : Set UnitPoint :=
  centeredSubinterval (1 / 2)

def centralQuarter : Set UnitPoint :=
  centeredSubinterval (1 / 4)

/-- The PYZ tangency parameter `Δ(f,g)`, normalized to `[0,1]`. -/
def tangencyParameter (f g : C2Function) : ℝ :=
  sInf {r : ℝ |
    ∃ x ∈ centralHalf,
      r = |f x - g x| + |f.firstDeriv x - g.firstDeriv x|}

/-- The tangency parameter over the centered half of an arbitrary interval. -/
def tangencyParameterOn (I : ParameterInterval) (f g : C2Function) : ℝ :=
  sInf {r : ℝ |
    ∃ x ∈ I.centeredCarrier (1 / 2),
      r = |f x - g x| + |f.firstDeriv x - g.firstDeriv x|}

/-- The sublevel set `E_δ = {x ∈ J/4 : |f(x)-g(x)| ≤ δ}`. -/
def tangencySublevelSet (f g : C2Function) (δ : ℝ) : Set UnitPoint :=
  {x | x ∈ centralQuarter ∧ |f x - g x| ≤ δ}

/-- The same sublevel set over the centered quarter of `I`. -/
def tangencySublevelSetOn (I : ParameterInterval) (f g : C2Function)
    (δ : ℝ) : Set UnitPoint :=
  {x | x ∈ I.centeredCarrier (1 / 4) ∧ |f x - g x| ≤ δ}

/-- A vertical graph neighborhood restricted to a parameter interval. -/
def verticalNeighborhoodOn (f : C2Function) (δ : ℝ)
    (I : ParameterInterval) : Set (UnitPoint × ℝ) :=
  {p | p.1 ∈ I.carrier ∧ |p.2 - f p.1| ≤ δ}

/-- A `(δ,t)` curvilinear rectangle from PYZ Definition 9. -/
structure CurvilinearRectangle (δ t : ℝ) where
  function : C2Function
  interval : ParameterInterval
  interval_length : interval.length = Real.sqrt (δ / t)

/--
The enlarged `(λδ,t)` rectangle from PYZ Definition 10 lies in the parameter
range where Definition 9 applies.
-/
def IsAdmissibleComparisonScale (δ t lambda : ℝ) : Prop :=
  1 ≤ lambda ∧ lambda * δ ≤ t

namespace CurvilinearRectangle

def carrier {δ t : ℝ} (R : CurvilinearRectangle δ t) :
    Set (UnitPoint × ℝ) :=
  verticalNeighborhoodOn R.function δ R.interval

def IsOverCentralQuarter {δ t : ℝ} (R : CurvilinearRectangle δ t) : Prop :=
  R.interval.carrier ⊆ centralQuarter

def IsOverCentralQuarterOf {δ t : ℝ} (R : CurvilinearRectangle δ t)
    (I : ParameterInterval) : Prop :=
  R.interval.carrier ⊆ I.centeredCarrier (1 / 4)

/-- PYZ Definition 11: `R` is `λ`-tangent to `f`. -/
def IsLambdaTangent {δ t : ℝ} (R : CurvilinearRectangle δ t)
    (f : C2Function) (lambda : ℝ) : Prop :=
  ∀ p ∈ R.carrier, |p.2 - f p.1| ≤ lambda * δ

/--
PYZ Definition 10: two rectangles fit in one thicker rectangle whose defining
function belongs to the same cinematic family.

The family-membership requirement is essential. Without it, an arbitrary
smooth transition between the two graphs can make unrelated rectangles
comparable, which is not the notion used in the paper.
-/
def AreLambdaComparable {δ t : ℝ} (R S : CurvilinearRectangle δ t)
    (family : Set C2Function) (lambda : ℝ) : Prop :=
  ∃ U : CurvilinearRectangle (lambda * δ) t,
    U.function ∈ family ∧ R.carrier ∪ S.carrier ⊆ U.carrier

def AreLambdaIncomparable {δ t : ℝ} (R S : CurvilinearRectangle δ t)
    (family : Set C2Function) (lambda : ℝ) : Prop :=
  ¬AreLambdaComparable R S family lambda

def intervalHullCarrier {δ t : ℝ} (R S : CurvilinearRectangle δ t) :
    Set UnitPoint :=
  {x |
    min R.interval.left S.interval.left ≤ (x : ℝ) ∧
      (x : ℝ) ≤ max R.interval.right S.interval.right}

/-- `small` is obtained by shrinking the parameter interval of `large`. -/
def IsCenteredShrinkOf {δ t : ℝ}
    (small large : CurvilinearRectangle δ t) (c : ℝ) : Prop :=
  small.function = large.function ∧
  small.interval.midpoint = large.interval.midpoint ∧
  small.interval.length = c * large.interval.length ∧
  small.interval.carrier ⊆ large.interval.carrier

end CurvilinearRectangle

/-- A finite indexed family of curvilinear rectangles. -/
structure RectangleFamily (δ t : ℝ) where
  card : ℕ
  rectangle : Fin card → CurvilinearRectangle δ t

/-- An indexed subfamily retaining the identity of each selected rectangle. -/
structure RectangleSubfamily {δ t : ℝ} (R : RectangleFamily δ t) where
  card : ℕ
  embedding : Fin card ↪ Fin R.card

namespace RectangleSubfamily

def family {δ t : ℝ} {R : RectangleFamily δ t}
    (S : RectangleSubfamily R) : RectangleFamily δ t where
  card := S.card
  rectangle i := R.rectangle (S.embedding i)

end RectangleSubfamily

namespace RectangleFamily

def IsPairwiseIncomparable {δ t : ℝ} (R : RectangleFamily δ t)
    (family : Set C2Function) (lambda : ℝ) : Prop :=
  ∀ i j, i ≠ j →
    (R.rectangle i).AreLambdaIncomparable (R.rectangle j) family lambda

def Nonempty {δ t : ℝ} (R : RectangleFamily δ t) : Prop :=
  0 < R.card

def CentersIn {δ t : ℝ} (R : RectangleFamily δ t)
    (family : Set C2Function) : Prop :=
  ∀ i, (R.rectangle i).function ∈ family

def IsOverCentralQuarter {δ t : ℝ} (R : RectangleFamily δ t) : Prop :=
  ∀ i, (R.rectangle i).IsOverCentralQuarter

def IsOverCentralQuarterOf {δ t : ℝ} (R : RectangleFamily δ t)
    (I : ParameterInterval) : Prop :=
  ∀ i, (R.rectangle i).IsOverCentralQuarterOf I

def tangentCount {δ t : ℝ} (R : CurvilinearRectangle δ t)
    (F : FiniteFunctionFamily) (lambda : ℝ) : ℕ := by
  classical
  exact (F.toFinset.filter fun f => R.IsLambdaTangent f lambda).card

theorem tangentCount_le_card {δ t : ℝ} (R : CurvilinearRectangle δ t)
    (F : FiniteFunctionFamily) (lambda : ℝ) :
    tangentCount R F lambda ≤ F.card := by
  classical
  unfold tangentCount
  calc
    (F.toFinset.filter fun f => R.IsLambdaTangent f lambda).card ≤
        F.toFinset.card :=
      Finset.card_filter_le _ _
    _ = F.card := by
      exact (Set.ncard_eq_toFinset_card F.carrier F.finite).symm

/-- The normalized cardinality appearing in PYZ Proposition 26. -/
def bipartiteNormalizedCount (W B : FiniteFunctionFamily)
    (mu nu : ℕ) : ℝ :=
  (W.card : ℝ) / (mu : ℝ) + (B.card : ℝ) / (nu : ℝ)

theorem two_le_bipartiteNormalizedCount_of_tangentCounts
    {δ t : ℝ} {R : RectangleFamily δ t}
    {W B : FiniteFunctionFamily} {mu nu : ℕ} {lambda : ℝ}
    (hR : R.Nonempty) (hmu : 0 < mu) (hnu : 0 < nu)
    (hcounts : ∀ i,
      mu ≤ tangentCount (R.rectangle i) W lambda ∧
      nu ≤ tangentCount (R.rectangle i) B lambda) :
    2 ≤ bipartiteNormalizedCount W B mu nu := by
  let i : Fin R.card := Classical.choice (Fin.pos_iff_nonempty.mp hR)
  have hmu_le : mu ≤ W.card :=
    (hcounts i).1.trans (tangentCount_le_card (R.rectangle i) W lambda)
  have hnu_le : nu ≤ B.card :=
    (hcounts i).2.trans (tangentCount_le_card (R.rectangle i) B lambda)
  have hmu_real : (0 : ℝ) < (mu : ℝ) := by exact_mod_cast hmu
  have hnu_real : (0 : ℝ) < (nu : ℝ) := by exact_mod_cast hnu
  have hW_real : (mu : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hmu_le
  have hB_real : (nu : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hnu_le
  have hW_ratio : 1 ≤ (W.card : ℝ) / (mu : ℝ) := by
    rw [le_div_iff₀ hmu_real]
    simpa using hW_real
  have hB_ratio : 1 ≤ (B.card : ℝ) / (nu : ℝ) := by
    rw [le_div_iff₀ hnu_real]
    simpa using hB_real
  unfold bipartiteNormalizedCount
  linarith

end RectangleFamily

namespace FiniteFunctionFamily

def HasNoExactTangenciesOn (F : FiniteFunctionFamily)
    (I : ParameterInterval) (shift : C2Function → ℝ) : Prop :=
  ∀ ⦃f⦄, f ∈ F.carrier →
    ∀ ⦃g⦄, g ∈ F.carrier → f ≠ g →
      ∀ x ∈ I.carrier,
        (f.verticalTranslate (shift f)) x ≠
            (g.verticalTranslate (shift g)) x ∨
          (f.verticalTranslate (shift f)).firstDeriv x ≠
            (g.verticalTranslate (shift g)).firstDeriv x

def DiameterLE (F : FiniteFunctionFamily) (diameter : ℝ) : Prop :=
  ∀ ⦃f⦄, f ∈ F.carrier →
    ∀ ⦃g⦄, g ∈ F.carrier → dist f g ≤ diameter

/-- PYZ Definition 12 for two finite function families. -/
def AreSeparated (W B : FiniteFunctionFamily) (t : ℝ) : Prop :=
  ∀ ⦃w⦄, w ∈ W.carrier →
    ∀ ⦃b⦄, b ∈ B.carrier → t ≤ dist w b

end FiniteFunctionFamily

/--
The parts of cinematic curvature used in Section 4, without the doubling
hypothesis.
-/
def HasCinematicCurvature (family : Set C2Function) (K : ℝ) : Prop :=
  (∀ ⦃f⦄, f ∈ family →
    ∀ ⦃g⦄, g ∈ family → c2Distance f g ≤ K) ∧
  (∀ ⦃f⦄, f ∈ family →
    ∀ ⦃g⦄, g ∈ family →
      ∀ x : UnitPoint,
        K⁻¹ * c2Distance f g ≤ jetGap f g x)

end Kakeya.Cinematic
