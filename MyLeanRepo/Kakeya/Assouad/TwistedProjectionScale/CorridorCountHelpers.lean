import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.PlanarGridCinematicCorridorCountStatement
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Helper lemmas for planar_grid_cinematic_corridor_count

These are intermediate lemmas used in the proof of the linear bound on the
number of grid cells meeting a bounded-slope cinematic corridor.
-/

noncomputable section

namespace Kakeya.Assouad

open Kakeya.Cinematic

/-- Bound on the difference of floors from a bound on the difference of reals. -/
lemma floor_diff_bound {x y C : ℝ} (h : |x - y| ≤ C) :
    |(⌊x⌋ : ℝ) - (⌊y⌋ : ℝ)| ≤ C + 1 := by
  have hxy : x - y ≤ C := (abs_le.mp h).2
  have hyx : y - x ≤ C := by linarith [(abs_le.mp h).1]
  have hfx : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have hfy : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
  have hltx : x < (⌊x⌋ : ℝ) + 1 :=
    (Int.floor_le_iff (z := ⌊x⌋)).mp le_rfl
  have hlty : y < (⌊y⌋ : ℝ) + 1 :=
    (Int.floor_le_iff (z := ⌊y⌋)).mp le_rfl
  have h1 : (⌊x⌋ : ℝ) - (⌊y⌋ : ℝ) ≤ C + 1 := by linarith
  have h2 : (⌊y⌋ : ℝ) - (⌊x⌋ : ℝ) ≤ C + 1 := by linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Each coordinate difference is bounded by the Euclidean distance. -/
lemma euclidean_coord_dist (p q : Point2) (i : Fin 2) :
    |p i - q i| ≤ dist p q := by
  have h1 : ‖(p - q) i‖ ≤ ‖p - q‖ := PiLp.norm_apply_le (p - q) i
  have h2 : (p - q) i = p i - q i := by simp
  have h3 : ‖p - q‖ = dist p q := by rfl
  have h4 : ‖p i - q i‖ = |p i - q i| := by
    simp [Real.norm_eq_abs]
  rw [h2, h4, h3] at h1
  exact h1

/-- Parametrize the cinematic graph over `[0,1]`. -/
def graphParam (g : C2Function) (t : ℝ) : Point2 :=
  g.extension t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
    t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

lemma graphParam_coord (g : C2Function) (t : ℝ) :
    (graphParam g t) 0 = g.extension t ∧
    (graphParam g t) 1 = t := by
  simp [graphParam]

lemma graph_eq_image (g : C2Function) :
    cinematicExtensionGraph g = graphParam g '' Set.Icc (0 : ℝ) 1 := by
  ext q
  simp only [cinematicExtensionGraph, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨q 1, h1, ?_⟩
    have h3 : q = graphParam g (q 1) := by
      ext i
      fin_cases i <;> simp [h2, graphParam_coord]
    exact h3.symm
  · rintro ⟨t, ht, rfl⟩
    have h := graphParam_coord g t
    have h1 : (graphParam g t) 1 ∈ Set.Icc (0 : ℝ) 1 := by
      rw [h.2]
      exact ht
    have h2 : (graphParam g t) 0 = g.extension ((graphParam g t) 1) := by
      rw [h.2, h.1]
    exact ⟨h1, h2⟩

/-- The cinematic extension graph over `[0,1]` is compact. -/
lemma graph_compact (g : C2Function) :
    IsCompact (cinematicExtensionGraph g) := by
  rw [graph_eq_image g]
  apply IsCompact.image (ConditionallyCompleteLinearOrder.isCompact_Icc (0 : ℝ) 1)
  have h1 : Continuous g.extension := g.extension_contDiff.continuous
  have h2 : Continuous (fun t : ℝ => g.extension t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) :=
    h1.smul continuous_const
  have h3 : Continuous (fun t : ℝ => t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) :=
    continuous_id.smul continuous_const
  exact h2.add h3

/-- The cinematic extension graph is nonempty. -/
lemma graph_nonempty (g : C2Function) :
    (cinematicExtensionGraph g).Nonempty := by
  rw [graph_eq_image g]
  refine ⟨graphParam g 0, 0, by norm_num, rfl⟩

/-- Extract a witnessing graph point from cthickening membership, using compactness. -/
lemma cthickening_extract (p : Point2) (g : C2Function)
    (r : ℝ) (hr : 0 ≤ r)
    (h : p ∈ Metric.cthickening r (cinematicExtensionGraph g)) :
    ∃ (q : Point2), q ∈ cinematicExtensionGraph g ∧ dist p q ≤ r := by
  have hc : IsCompact (cinematicExtensionGraph g) := graph_compact g
  have hne : (cinematicExtensionGraph g).Nonempty := graph_nonempty g
  have h1 : Metric.infEDist p (cinematicExtensionGraph g) ≤ ENNReal.ofReal r :=
    Metric.mem_cthickening_iff.mp h
  rcases hc.exists_infEDist_eq_edist hne p with ⟨q, hq, h2⟩
  have h3 : edist p q ≤ ENNReal.ofReal r := by
    rw [←h2]
    exact h1
  have h4 : dist p q ≤ r := (edist_le_ofReal hr).mp h3
  exact ⟨q, hq, h4⟩

/-- If two reals have the same floor, their difference is strictly less than 1. -/
lemma same_floor_close (x y : ℝ) (h : ⌊x⌋ = ⌊y⌋) : |x - y| < 1 := by
  have h1 : x < (⌊x⌋ : ℝ) + 1 :=
    (Int.floor_le_iff (z := ⌊x⌋)).mp le_rfl
  have h2 : y < (⌊y⌋ : ℝ) + 1 :=
    (Int.floor_le_iff (z := ⌊y⌋)).mp le_rfl
  have h3 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have h4 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
  have heq : (⌊x⌋ : ℝ) = (⌊y⌋ : ℝ) := by exact_mod_cast h
  have h5 : x - y < 1 := by linarith
  have h6 : y - x < 1 := by linarith
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end Kakeya.Assouad
