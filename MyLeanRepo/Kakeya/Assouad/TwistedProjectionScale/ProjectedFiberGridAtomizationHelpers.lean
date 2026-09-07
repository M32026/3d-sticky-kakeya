import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberGridAtomizationStatement
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Helper lemmas for projected-fiber grid atomization

Geometric facts about planar grid centers, indices, atoms, and pullback
shading monotonicity.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

private lemma floor_int_add_half (n : ℤ) :
    ⌊(n : ℝ) + 1 / 2⌋ = n := by
  rw [Int.floor_eq_iff]
  constructor <;> norm_num

private lemma planarGridCenter_coord0
    (base levels : ℕ) (idx : ℤ × ℤ) :
    (planarGridCenter base levels idx) 0 =
      ((idx.1 : ℝ) + 1 / 2) /
        (base ^ levels : ℝ) := by
  simp [planarGridCenter, EuclideanSpace.single_apply] <;> ring

private lemma planarGridCenter_coord1
    (base levels : ℕ) (idx : ℤ × ℤ) :
    (planarGridCenter base levels idx) 1 =
      ((idx.2 : ℝ) + 1 / 2) /
        (base ^ levels : ℝ) := by
  simp [planarGridCenter, EuclideanSpace.single_apply] <;> ring

lemma planarGridIndex_center_eq
    (base levels : ℕ) (idx : ℤ × ℤ) (hbase : 3 ≤ base) :
    planarGridIndex base levels
      (planarGridCenter base levels idx) = idx := by
  have h_pos : (0 : ℝ) < (base ^ levels : ℝ) := by positivity
  have hcoord0 :
      (planarGridCenter base levels idx) 0 *
          (base ^ levels : ℝ) =
        (idx.1 : ℝ) + 1 / 2 := by
    rw [planarGridCenter_coord0]
    field_simp [h_pos.ne'] <;> ring
  have hcoord1 :
      (planarGridCenter base levels idx) 1 *
          (base ^ levels : ℝ) =
        (idx.2 : ℝ) + 1 / 2 := by
    rw [planarGridCenter_coord1]
    field_simp [h_pos.ne'] <;> ring
  dsimp only [planarGridIndex]
  rw [hcoord0, hcoord1]
  rw [floor_int_add_half idx.1, floor_int_add_half idx.2] <;> rfl

lemma planarGridCenter_injective
    (base levels : ℕ) (hbase : 3 ≤ base) :
    Function.Injective (planarGridCenter base levels) := by
  intro idx1 idx2 h
  have h_pos : (0 : ℝ) < (base ^ levels : ℝ) := by positivity
  have h1 :
      (planarGridCenter base levels idx1) 0 =
        (planarGridCenter base levels idx2) 0 := by
    rw [h]
  have h2 :
      (planarGridCenter base levels idx1) 1 =
        (planarGridCenter base levels idx2) 1 := by
    rw [h]
  have h3 :
      ((idx1.1 : ℝ) + 1 / 2) /
          (base ^ levels : ℝ) =
        ((idx2.1 : ℝ) + 1 / 2) /
          (base ^ levels : ℝ) := by
    rw [planarGridCenter_coord0, planarGridCenter_coord0] at h1
    exact h1
  have h4 :
      ((idx1.2 : ℝ) + 1 / 2) /
          (base ^ levels : ℝ) =
        ((idx2.2 : ℝ) + 1 / 2) /
          (base ^ levels : ℝ) := by
    rw [planarGridCenter_coord1, planarGridCenter_coord1] at h2
    exact h2
  have h5 : (idx1.1 : ℝ) = (idx2.1 : ℝ) := by
    field_simp [h_pos.ne'] at h3 <;> linarith
  have h6 : (idx1.2 : ℝ) = (idx2.2 : ℝ) := by
    field_simp [h_pos.ne'] at h4 <;> linarith
  have h7 : idx1.1 = idx2.1 := by exact_mod_cast h5
  have h8 : idx1.2 = idx2.2 := by exact_mod_cast h6
  exact Prod.ext h7 h8

private lemma int_abs_diff_pos {a b : ℤ} (h : a ≠ b) :
    |a - b| ≥ 1 := by
  have h1 : a - b ≠ 0 := by omega
  have h2 : 0 < |a - b| := abs_pos.mpr h1
  omega

private lemma int_abs_diff_pos_real {a b : ℤ} (h : a ≠ b) :
    |(a : ℝ) - (b : ℝ)| ≥ 1 := by
  have h1 : |a - b| ≥ 1 := int_abs_diff_pos h
  have h2 : |(a : ℝ) - (b : ℝ)| = ↑(|a - b|) := by
    simp [Int.cast_sub] <;> rfl
  rw [h2]
  exact_mod_cast h1

private lemma abs_div_pos {a : ℝ} {b : ℝ} (hb : 0 < b) :
    |a / b| = |a| / b := by
  rw [abs_div, abs_of_pos hb]

lemma planarGridCenter_separated
    (base levels : ℕ) (idx1 idx2 : ℤ × ℤ)
    (hbase : 3 ≤ base) (hne : idx1 ≠ idx2) :
    dist (planarGridCenter base levels idx1)
        (planarGridCenter base levels idx2) ≥
      (base ^ levels : ℝ)⁻¹ := by
  have h_pos : (0 : ℝ) < (base ^ levels : ℝ) := by positivity
  set c1 := planarGridCenter base levels idx1 with hc1
  set c2 := planarGridCenter base levels idx2 with hc2
  have hne' : idx1.1 ≠ idx2.1 ∨ idx1.2 ≠ idx2.2 := by
    by_contra h
    push Not at h
    exact hne (Prod.ext h.1 h.2)
  have h_inv :
      (base ^ levels : ℝ)⁻¹ =
        1 / (base ^ levels : ℝ) := by
    rw [inv_eq_one_div]
  rcases hne' with h | h
  · have hdiff :
        |(idx1.1 : ℝ) - (idx2.1 : ℝ)| ≥ 1 :=
      int_abs_diff_pos_real h
    have hcalc :
        |c1 0 - c2 0| =
          |(idx1.1 : ℝ) - (idx2.1 : ℝ)| /
            (base ^ levels : ℝ) := by
      rw [planarGridCenter_coord0, planarGridCenter_coord0]
      have h_eq :
          ((idx1.1 : ℝ) + 1 / 2) /
                (base ^ levels : ℝ) -
              ((idx2.1 : ℝ) + 1 / 2) /
                (base ^ levels : ℝ) =
            ((idx1.1 : ℝ) - (idx2.1 : ℝ)) /
              (base ^ levels : ℝ) := by
        field_simp [h_pos.ne'] <;> ring
      rw [h_eq, abs_div_pos h_pos]
    have h9 :
        |(idx1.1 : ℝ) - (idx2.1 : ℝ)| /
              (base ^ levels : ℝ) ≥
            1 / (base ^ levels : ℝ) := by
      apply div_le_div_of_nonneg_right hdiff
      positivity
    calc
      dist c1 c2 = ‖c1 - c2‖ := by rfl
      _ ≥ |(c1 - c2) 0| := by
        have hnorm :
            ‖(c1 - c2) 0‖ ≤ ‖c1 - c2‖ :=
          PiLp.norm_apply_le (c1 - c2) 0
        simpa [Real.norm_eq_abs] using hnorm
      _ = |c1 0 - c2 0| := by simp
      _ = |(idx1.1 : ℝ) - (idx2.1 : ℝ)| /
          (base ^ levels : ℝ) := hcalc
      _ ≥ 1 / (base ^ levels : ℝ) := h9
      _ = (base ^ levels : ℝ)⁻¹ := h_inv.symm
  · have hdiff :
        |(idx1.2 : ℝ) - (idx2.2 : ℝ)| ≥ 1 :=
      int_abs_diff_pos_real h
    have hcalc :
        |c1 1 - c2 1| =
          |(idx1.2 : ℝ) - (idx2.2 : ℝ)| /
            (base ^ levels : ℝ) := by
      rw [planarGridCenter_coord1, planarGridCenter_coord1]
      have h_eq :
          ((idx1.2 : ℝ) + 1 / 2) /
                (base ^ levels : ℝ) -
              ((idx2.2 : ℝ) + 1 / 2) /
                (base ^ levels : ℝ) =
            ((idx1.2 : ℝ) - (idx2.2 : ℝ)) /
              (base ^ levels : ℝ) := by
        field_simp [h_pos.ne'] <;> ring
      rw [h_eq, abs_div_pos h_pos]
    have h9 :
        |(idx1.2 : ℝ) - (idx2.2 : ℝ)| /
              (base ^ levels : ℝ) ≥
            1 / (base ^ levels : ℝ) := by
      apply div_le_div_of_nonneg_right hdiff
      positivity
    calc
      dist c1 c2 = ‖c1 - c2‖ := by rfl
      _ ≥ |(c1 - c2) 1| := by
        have hnorm :
            ‖(c1 - c2) 1‖ ≤ ‖c1 - c2‖ :=
          PiLp.norm_apply_le (c1 - c2) 1
        simpa [Real.norm_eq_abs] using hnorm
      _ = |c1 1 - c2 1| := by simp
      _ = |(idx1.2 : ℝ) - (idx2.2 : ℝ)| /
          (base ^ levels : ℝ) := hcalc
      _ ≥ 1 / (base ^ levels : ℝ) := h9
      _ = (base ^ levels : ℝ)⁻¹ := h_inv.symm

lemma planarGridIndex_measurable (base levels : ℕ) :
    Measurable
      (planarGridIndex base levels : Point2 → ℤ × ℤ) := by
  have h1 : Measurable (fun p : Point2 => p 0) := by fun_prop
  have h2 : Measurable (fun p : Point2 => p 1) := by fun_prop
  have h3 :
      Measurable
        (fun p : Point2 => p 0 * (base ^ levels : ℝ)) :=
    h1.mul measurable_const
  have h4 :
      Measurable
        (fun p : Point2 => p 1 * (base ^ levels : ℝ)) :=
    h2.mul measurable_const
  exact h3.floor.prod h4.floor

lemma gridAtom_measurable
    (band : Set Point2) (base levels : ℕ) (center : Point2)
    (hband : MeasurableSet band) :
    MeasurableSet
      (projectedFiberGridAtom band base levels center) := by
  have h1 : Measurable (planarGridIndex base levels) :=
    planarGridIndex_measurable base levels
  have h2 :
      MeasurableSet
        {q : Point2 |
          planarGridIndex base levels q =
            planarGridIndex base levels center} :=
    h1 (MeasurableSet.singleton _)
  exact hband.inter h2

lemma gridAtom_disjoint
    (band : Set Point2) (base levels : ℕ) (c1 c2 : Point2)
    (h :
      planarGridIndex base levels c1 ≠
        planarGridIndex base levels c2) :
    Disjoint
      (projectedFiberGridAtom band base levels c1)
      (projectedFiberGridAtom band base levels c2) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  exact h (hx1.2.symm.trans hx2.2)

lemma gridAtom_posMass_injective
    {base levels indexBound : ℕ}
    {band : Set Point2} {μ : Measure Point2}
    {z1 z2 : Point2}
    (hbase : 3 ≤ base)
    (hz1 : z1 ∈ boundedPlanarGridCenters base levels indexBound)
    (hz2 : z2 ∈ boundedPlanarGridCenters base levels indexBound)
    (hpos : μ (projectedFiberGridAtom band base levels z1) ≠ 0)
    (heq :
      projectedFiberGridAtom band base levels z1 =
        projectedFiberGridAtom band base levels z2) :
    z1 = z2 := by
  by_cases h : z1 = z2
  · exact h
  · rcases Finset.mem_image.mp hz1 with ⟨idx1, _, rfl⟩
    rcases Finset.mem_image.mp hz2 with ⟨idx2, _, rfl⟩
    have hne_idx : idx1 ≠ idx2 := by
      intro he
      exact h (by rw [he])
    have h_grid :
        planarGridIndex base levels
            (planarGridCenter base levels idx1) ≠
          planarGridIndex base levels
            (planarGridCenter base levels idx2) := by
      rw [planarGridIndex_center_eq base levels idx1 hbase,
        planarGridIndex_center_eq base levels idx2 hbase]
      exact hne_idx
    have h_disj :=
      gridAtom_disjoint band base levels _ _ h_grid
    have h_empty :
        projectedFiberGridAtom band base levels
            (planarGridCenter base levels idx1) = ∅ := by
      apply Set.subset_empty_iff.mp
      intro x hx
      have hx2 :
          x ∈ projectedFiberGridAtom band base levels
            (planarGridCenter base levels idx2) := by
        rw [heq] at hx
        exact hx
      exact (Set.disjoint_left.mp h_disj) hx hx2
    rw [h_empty] at hpos
    simp at hpos

lemma pullbackSubshading_mono
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction)
    (X1 X2 : Set Point2)
    (hX1 : MeasurableSet X1)
    (hX2 : MeasurableSet X2)
    (hsub : X1 ⊆ X2) :
    IsSubshading
      (projectionPullbackShading Y f X1 hX1)
      (projectionPullbackShading Y f X2 hX2) := by
  intro i x hx
  exact ⟨hx.1, hsub hx.2⟩

end Kakeya.Assouad
