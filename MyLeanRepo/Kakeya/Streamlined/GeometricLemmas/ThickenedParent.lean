import MyLeanRepo.Kakeya.Streamlined.VolumeHelpers
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Thickening a coarse parent

The full shortest-scale thickening of a fine body need not stay inside its
original coarse parent.  This module records the paper-faithful replacement:
thicken the parent by the same radius.  The enlarged parent remains convex,
measurable, and comparable to the original parent dimensions.
-/

noncomputable section

open Metric

namespace Kakeya.Streamlined

/-- A body obtained by closed metric thickening. -/
def thickenedBody (W : Body) (r : ℝ) : Body :=
  ⟨Metric.cthickening r W.carrier⟩

/-- Thicken every member of an indexed body family by the same radius. -/
def BodyFamily.thicken (F : BodyFamily) (r : ℝ) : BodyFamily where
  card := F.card
  body i := thickenedBody (F.body i) r

lemma BodyFamily.thicken_isMeasurable (F : BodyFamily) (r : ℝ) :
    (F.thicken r).IsMeasurable := by
  intro i
  exact Metric.isClosed_cthickening.measurableSet

lemma BodyFamily.thicken_isConvex (F : BodyFamily) (r : ℝ)
    (hF : F.IsConvex) :
    (F.thicken r).IsConvex := by
  intro i
  exact Convex.cthickening (hF i) r

namespace Factoring

/--
Thickening both sides of a factoring preserves its parent map and
surjectivity.
-/
def thicken {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (r : ℝ) :
    Factoring (fine.thicken r) (coarse.thicken r) where
  parent := P.parent
  parent_surjective := P.parent_surjective
  contained i := Metric.cthickening_subset_of_subset r (P.contained i)

@[simp] lemma thicken_parent {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (r : ℝ) (i : Fin fine.card) :
    (P.thicken r).parent i = P.parent i := rfl

/-- Thickening a factoring does not change any parent fiber. -/
@[simp] lemma thicken_fiberIndices {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (r : ℝ) (j : Fin coarse.card) :
    (P.thicken r).fiberIndices j = P.fiberIndices j := by
  rfl

/--
Enlarge only the coarse family.  The original fine members remain contained
because each coarse carrier is contained in its own closed thickening.
-/
def enlargeCoarse {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (r : ℝ) :
    Factoring fine (coarse.thicken r) where
  parent := P.parent
  parent_surjective := P.parent_surjective
  contained i :=
    (P.contained i).trans
      (Metric.self_subset_cthickening (coarse.body (P.parent i)).carrier)

@[simp] lemma enlargeCoarse_parent {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (r : ℝ) (i : Fin fine.card) :
    (P.enlargeCoarse r).parent i = P.parent i := rfl

@[simp] lemma enlargeCoarse_fiberIndices {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (r : ℝ) (j : Fin coarse.card) :
    (P.enlargeCoarse r).fiberIndices j = P.fiberIndices j := by
  rfl

@[simp] lemma enlargeCoarse_fiberMass {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (r : ℝ) (j : Fin coarse.card) :
    (P.enlargeCoarse r).fiberMass j = P.fiberMass j := by
  rfl

@[simp] lemma enlargeCoarse_fiberContainedMass
    {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (r : ℝ) (j : Fin coarse.card)
    (K : Set Point3) :
    (P.enlargeCoarse r).fiberContainedMass j K =
      P.fiberContainedMass j K := by
  rfl

@[simp] lemma enlargeCoarse_fiberShadedMass
    {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (Y : Shading fine)
    (r : ℝ) (j : Fin coarse.card) :
    (P.enlargeCoarse r).fiberShadedMass Y j =
      P.fiberShadedMass Y j := by
  rfl

@[simp] lemma enlargeCoarse_fiberShadedUnion
    {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (Y : Shading fine)
    (r : ℝ) (j : Fin coarse.card) :
    (P.enlargeCoarse r).fiberShadedUnion Y j =
      P.fiberShadedUnion Y j := by
  rfl

@[simp] lemma enlargeCoarse_fiberAverageMultiplicityLE
    {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (Y : Shading fine)
    (r : ℝ) (j : Fin coarse.card) (M : ENNReal) :
    (P.enlargeCoarse r).FiberAverageMultiplicityLE Y j M ↔
      P.FiberAverageMultiplicityLE Y j M := by
  simp only [Factoring.FiberAverageMultiplicityLE,
    enlargeCoarse_fiberShadedMass, enlargeCoarse_fiberShadedUnion]

/--
Frostman control survives enlargement of every coarse parent, with loss equal
to a uniform bound for the enlarged-to-original parent volume ratio.
-/
lemma enlargeCoarse_fibersAreCFrostman
    {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (r : ℝ) (C Q : ENNReal)
    (hcoarse_convex : coarse.IsConvex)
    (hfrostman : P.FibersAreCFrostman C)
    (hvolume :
      ∀ j, ((coarse.thicken r).body j).volume ≤
        Q * (coarse.body j).volume) :
    (P.enlargeCoarse r).FibersAreCFrostman (Q * C) := by
  classical
  intro j K hK_conv _hK_sub
  let W := (coarse.body j).carrier
  let K' := K ∩ W
  have hK'_conv : Convex ℝ K' :=
    hK_conv.inter (hcoarse_convex j)
  have hK'_sub : K' ⊆ W := Set.inter_subset_right
  have hindices :
      (P.fiberIndices j).filter
          (fun i => (fine.body i).carrier ⊆ K) =
        (P.fiberIndices j).filter
          (fun i => (fine.body i).carrier ⊆ K') := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi_fiber, hiK⟩
      have hparent : P.parent i = j :=
        (Finset.mem_filter.mp hi_fiber).2
      have hiW : (fine.body i).carrier ⊆ W := by
        intro x hx
        have hx' := P.contained i hx
        simpa [W, hparent] using hx'
      exact ⟨hi_fiber, fun x hx => ⟨hiK hx, hiW hx⟩⟩
    · rintro ⟨hi_fiber, hiK'⟩
      exact ⟨hi_fiber, hiK'.trans Set.inter_subset_left⟩
  have hcontained :
      P.fiberContainedMass j K =
        P.fiberContainedMass j K' := by
    dsimp only [Factoring.fiberContainedMass]
    rw [hindices]
  have hold :
      P.fiberContainedMass j K' * (coarse.body j).volume ≤
        C * P.fiberMass j * MeasureTheory.volume K' :=
    hfrostman j K' hK'_conv hK'_sub
  have hK'_volume :
      MeasureTheory.volume K' ≤ MeasureTheory.volume K :=
    MeasureTheory.measure_mono Set.inter_subset_left
  calc
    (P.enlargeCoarse r).fiberContainedMass j K *
          ((coarse.thicken r).body j).volume
        = P.fiberContainedMass j K *
            ((coarse.thicken r).body j).volume := by rfl
    _ ≤ P.fiberContainedMass j K *
          (Q * (coarse.body j).volume) := by
        exact mul_le_mul_left' (hvolume j) _
    _ = Q * (P.fiberContainedMass j K *
          (coarse.body j).volume) := by ring
    _ = Q * (P.fiberContainedMass j K' *
          (coarse.body j).volume) := by rw [hcontained]
    _ ≤ Q * (C * P.fiberMass j * MeasureTheory.volume K') := by
        exact mul_le_mul_left' hold Q
    _ ≤ Q * (C * P.fiberMass j * MeasureTheory.volume K) := by
        exact mul_le_mul_left' (mul_le_mul_left' hK'_volume (C * P.fiberMass j)) Q
    _ = (Q * C) * (P.enlargeCoarse r).fiberMass j *
          MeasureTheory.volume K := by
        change Q * (C * P.fiberMass j * MeasureTheory.volume K) =
          (Q * C) * P.fiberMass j * MeasureTheory.volume K
        ring

/--
The exact induced shading on an enlarged coarse family.
-/
def enlargedCoarseShading {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (Y : Shading fine) (r : ℝ) :
    Shading (coarse.thicken r) where
  carrier j :=
    ((coarse.thicken r).body j).carrier ∩
      Metric.cthickening r
        {x | ∃ i : Fin fine.card, P.parent i = j ∧ x ∈ Y.carrier i}
  measurable_carrier j :=
    Metric.isClosed_cthickening.measurableSet.inter
      Metric.isClosed_cthickening.measurableSet
  subset_body j := Set.inter_subset_left

lemma enlargeCoarse_isExactInducedShading {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (Y : Shading fine) (r : ℝ) :
    (P.enlargeCoarse r).IsExactInducedShading Y
      (P.enlargedCoarseShading Y r) r := by
  intro j
  rfl

/--
For an enlarged parent, the exact induced shading is the full thickening:
the intersection with the enlarged parent is redundant.
-/
lemma enlargedCoarseShading_carrier_eq {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (Y : Shading fine) (r : ℝ)
    (j : Fin coarse.card) :
    (P.enlargedCoarseShading Y r).carrier j =
      Metric.cthickening r
        {x | ∃ i : Fin fine.card, P.parent i = j ∧ x ∈ Y.carrier i} := by
  apply Set.inter_eq_right.mpr
  apply Metric.cthickening_subset_of_subset
  rintro x ⟨i, hi, hx⟩
  have hx_fine : x ∈ (fine.body i).carrier := Y.subset_body i hx
  have hx_coarse : x ∈ (coarse.body (P.parent i)).carrier :=
    P.contained i hx_fine
  simpa [hi] using hx_coarse

end Factoring

namespace GeometricLemmas

/--
The `r`-thickening of an axis-aligned box lies in the box whose side lengths
are enlarged by `4r`.  The relaxed constant avoids any closedness hypothesis:
we place each point of the closed `r`-thickening in a closed `2r`-ball around
the original set.
-/
lemma cthickening_axisBox_subset
    (a b c r : ℝ) (hr : 0 < r) :
    Metric.cthickening r (axisBox a b c) ⊆
      axisBox (a + 4 * r) (b + 4 * r) (c + 4 * r) := by
  intro x hx
  have hsub :
      Metric.cthickening r (axisBox a b c) ⊆
        ⋃ y ∈ axisBox a b c, Metric.closedBall y (2 * r) :=
    Metric.cthickening_subset_iUnion_closedBall_of_lt
      (axisBox a b c) (by positivity) (by linarith)
  rcases Set.mem_iUnion₂.mp (hsub hx) with ⟨y, hy, hxy⟩
  have hcoord : ∀ i : Fin 3, |x i - y i| ≤ 2 * r := by
    intro i
    calc
      |x i - y i| = dist (x i) (y i) := by
        rw [Real.dist_eq]
      _ ≤ dist x y := PiLp.dist_apply_le x y i
      _ ≤ 2 * r := hxy
  have hbound : ∀ i : Fin 3, ∀ d : ℝ,
      |y i| ≤ d / 2 → |x i| ≤ (d + 4 * r) / 2 := by
    intro i d hyi
    calc
      |x i| = |y i + (x i - y i)| := by ring_nf
      _ ≤ |y i| + |x i - y i| := abs_add_le _ _
      _ ≤ d / 2 + 2 * r := add_le_add hyi (hcoord i)
      _ = (d + 4 * r) / 2 := by ring
  exact ⟨hbound 0 a hy.1, hbound 1 b hy.2.1, hbound 2 c hy.2.2⟩

/--
If `V ⊆ W`, then their closed `r`-thickenings satisfy the same inclusion.
-/
lemma cthickening_subset_cthickening {V W : Set Point3} (r : ℝ)
    (hVW : V ⊆ W) :
    Metric.cthickening r V ⊆ Metric.cthickening r W :=
  Metric.cthickening_subset_of_subset r hVW

/--
Thickening an `r × s × t` convex parent by its shortest scale produces a
measurable convex parent with the same displayed dimensions and comparability
factor `B + 4`.  It contains the corresponding thickening of every subbody.
-/
lemma thickened_parent_geometry
    (B r s t : ℝ)
    (hB : 1 ≤ B)
    (hr : 0 < r) (hrs : r ≤ s) (hst : s ≤ t)
    (W : Body) (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (hWdim : W.HasDimensionsInFrame frame r s t B)
    (hWconvex : W.IsConvex) :
    let W' := thickenedBody W r
    W'.IsMeasurable ∧
      W'.IsConvex ∧
      W'.HasDimensionsInFrame frame r s t (B + 4) ∧
      ∀ V : Body, V.carrier ⊆ W.carrier →
        Metric.cthickening r V.carrier ⊆ W'.carrier := by
  let W' := thickenedBody W r
  have hinner :
      frame '' axisBox r s t ⊆ W'.carrier := by
    exact hWdim.2.2.2.2.1 |>.trans (Metric.self_subset_cthickening W.carrier)
  have houter :
      W'.carrier ⊆ frame '' axisBox ((B + 4) * r) ((B + 4) * s) ((B + 4) * t) := by
    intro x hx
    have hx_outer :
        x ∈ Metric.cthickening r
          (frame '' axisBox (B * r) (B * s) (B * t)) := by
      exact Metric.cthickening_subset_of_subset r hWdim.2.2.2.2.2 hx
    have hdist :
        frame.symm x ∈ Metric.cthickening r (axisBox (B * r) (B * s) (B * t)) := by
      have himage :=
        Metric.infEDist_image frame.toIsometryEquiv.isometry
          (x := frame.symm x) (t := axisBox (B * r) (B * s) (B * t))
      have hx_dist :
          Metric.infEDist x
              (frame '' axisBox (B * r) (B * s) (B * t)) ≤
            ENNReal.ofReal r := hx_outer
      simpa using (show
        Metric.infEDist (frame.symm x)
            (axisBox (B * r) (B * s) (B * t)) ≤ ENNReal.ofReal r by
          rw [← himage]
          simpa using hx_dist)
    have hbox := cthickening_axisBox_subset (B * r) (B * s) (B * t) r hr hdist
    refine ⟨frame.symm x, ?_, frame.apply_symm_apply x⟩
    constructor
    · calc
        |(frame.symm x) 0| ≤ (B * r + 4 * r) / 2 := hbox.1
        _ = ((B + 4) * r) / 2 := by ring
    constructor
    · calc
        |(frame.symm x) 1| ≤ (B * s + 4 * r) / 2 := hbox.2.1
        _ ≤ (B * s + 4 * s) / 2 := by gcongr
        _ = ((B + 4) * s) / 2 := by ring
    · calc
        |(frame.symm x) 2| ≤ (B * t + 4 * r) / 2 := hbox.2.2
        _ ≤ (B * t + 4 * t) / 2 := by gcongr; linarith
        _ = ((B + 4) * t) / 2 := by ring
  refine ⟨Metric.isClosed_cthickening.measurableSet,
    Convex.cthickening hWconvex r, ?_, ?_⟩
  · exact ⟨hr, hrs, hst, by linarith, hinner, houter⟩
  · intro V hVW
    exact cthickening_subset_cthickening r hVW

/--
The enlarged parent has volume at most `(B + 4)³` times the original parent.
-/
lemma thickened_parent_volume_le
    (B r s t : ℝ)
    (hB : 1 ≤ B)
    (hr : 0 < r) (hrs : r ≤ s) (hst : s ≤ t)
    (W : Body) (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (hWdim : W.HasDimensionsInFrame frame r s t B)
    (hWconvex : W.IsConvex) :
    (thickenedBody W r).volume ≤
      ENNReal.ofReal ((B + 4) ^ 3) * W.volume := by
  have hW'dim :
      (thickenedBody W r).HasDimensionsInFrame frame r s t (B + 4) :=
    (thickened_parent_geometry B r s t hB hr hrs hst W frame hWdim hWconvex).2.2.1
  have hupper :
      (thickenedBody W r).volume ≤
        ENNReal.ofReal ((B + 4) ^ 3 * r * s * t) :=
    hasDimensionsInFrame_volume_upper hW'dim
  have hlower : ENNReal.ofReal (r * s * t) ≤ W.volume :=
    hasDimensionsInFrame_volume_lower hWdim
  calc
    (thickenedBody W r).volume
        ≤ ENNReal.ofReal ((B + 4) ^ 3 * r * s * t) := hupper
    _ = ENNReal.ofReal ((B + 4) ^ 3) * ENNReal.ofReal (r * s * t) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      ring_nf
    _ ≤ ENNReal.ofReal ((B + 4) ^ 3) * W.volume := by
      gcongr

end GeometricLemmas

end Kakeya.Streamlined
